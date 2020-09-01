#請從最底下main部分開始執行
#請自行更改function setwd路徑

install.packages("rJava")
install.packages("Rwordseg", repos="http://R-Forge.R-project.org")
install.packages("tm")
install.packages("tmcn", repos="http://R-Forge.R-project.org", type="source")
install.packages("wordcloud")
install.packages("XML")
install.packages("knitr")
install.packages("RCurl")
install.packages("rvest")
install.packages('stringr')
install.packages("cidian")
install.packages("devtools")
install.packages("RColorBrewer")
install_github("qinwf/cidian")
librery(cidian)
library(stringr)
library(rJava)
library(httr)
library(Rwordseg)
library(XML)
library(RCurl)
library(rvest)
library(knitr)
library(tm)
library(tmcn)
library(devtools)
library("slam")
library(wordcloud)
#----------------------------------------------------------------------------------
wordsCN<-function(x,...){
  words<-unlist(segmentCN(x))
  return(words)
}
##  Modified command "termFreq" on package tm
termFreqCN<-
  function (doc, control = list()) 
  {
    #stopifnot(inherits(doc, "TextDocument"), is.list(control))
    .tokenize <- control$tokenize
    if (is.null(.tokenize) || identical(.tokenize, "wordsCN")) 
      .tokenize <- wordsCN
    else if (identical(.tokenize, "MC")) 
      .tokenize <- MC_tokenizer
    else if (identical(.tokenize, "scan")) 
      .tokenize <- scan_tokenizer
    else if (NLP::is.Span_Tokenizer(.tokenize)) 
      .tokenize <- NLP::as.Token_Tokenizer(.tokenize)
    if (is.function(.tokenize)) 
      txt <- .tokenize(doc)
    else stop("invalid tokenizer")
    .tolower <- control$tolower
    if (is.null(.tolower) || isTRUE(.tolower)) 
      .tolower <- tolower
    if (is.function(.tolower)) 
      txt <- .tolower(txt)
    .removePunctuation <- control$removePunctuation
    if (isTRUE(.removePunctuation)) 
      .removePunctuation <- removePunctuation
    else if (is.list(.removePunctuation)) 
      .removePunctuation <- function(x) do.call(removePunctuation, 
                                                c(list(x), control$removePunctuation))
    .removeNumbers <- control$removeNumbers
    if (isTRUE(.removeNumbers)) 
      .removeNumbers <- removeNumbers
    .stopwords <- control$stopwords
    if (isTRUE(.stopwords)) 
      .stopwords <- function(x) x[is.na(match(x, stopwords(meta(doc, 
                                                                "language"))))]
    else if (is.character(.stopwords)) 
      .stopwords <- function(x) x[is.na(match(x, control$stopwords))]
    .stemming <- control$stemming
    if (isTRUE(.stemming)) 
      .stemming <- function(x) stemDocument(x, meta(doc, "language"))
    or <- c("removePunctuation", "removeNumbers", "stopwords", 
            "stemming")
    nc <- names(control)
    n <- nc[nc %in% or]
    for (name in sprintf(".%s", c(n, setdiff(or, n)))) {
      g <- get(name)
      if (is.function(g)) 
        txt <- g(txt)
    }
    if (is.null(txt)) 
      return(setNames(integer(0), character(0)))
    dictionary <- control$dictionary
    tab <- if (is.null(dictionary)) 
      table(txt)
    else table(factor(txt, levels = dictionary))
    if (names(tab[1])=="") tab <- tab[-1]
    bl <- control$bounds$local
    if (length(bl) == 2L && is.numeric(bl)) 
      tab <- tab[(tab >= bl[1]) & (tab <= bl[2])]
    nc <- nchar(names(tab), type = "chars")
    wl <- control$wordLengths
    lb <- if (is.numeric(wl[1])) wl[1] else 3
    ub <- if (is.numeric(wl[2])) wl[2] else Inf
    tab <- tab[(nc >= lb) & (nc <= ub)]
    storage.mode(tab) <- "integer"
    class(tab) <- c("term_frequency", class(tab))
    tab
  }

## Useful for TermDocumentMatrix
TermDocumentMatrix_classes <-
  c("TermDocumentMatrix", "simple_triplet_matrix")
## Useful for TermDocumentMatrix
.TermDocumentMatrix <-
  function(x, weighting)
  {
    x <- as.simple_triplet_matrix(x)
    if(!is.null(dimnames(x)))
      names(dimnames(x)) <- c("Terms", "Docs")
    class(x) <- TermDocumentMatrix_classes
    ## <NOTE>
    ## Note that if weighting is a weight function, it already needs to
    ## know whether we have a term-document or document-term matrix.
    ##
    ## Ideally we would require weighting to be a WeightFunction object
    ## or a character string of length 2.  But then
    ##   dtm <- DocumentTermMatrix(crude,
    ##                             control = list(weighting =
    ##                                            function(x)
    ##                                            weightTfIdf(x, normalize =
    ##                                                        FALSE),
    ##                                            stopwords = TRUE))
    ## in example("DocumentTermMatrix") fails [because weightTfIdf() is
    ## a weight function and not a weight function generator ...]
    ## Hence, for now, instead of
    ##   if(inherits(weighting, "WeightFunction"))
    ##      x <- weighting(x)
    ## use
    if(is.function(weighting))
      x <- weighting(x)
    ## and hope for the best ...
    ## </NOTE>
    else if(is.character(weighting) && (length(weighting) == 2L))
      attr(x, "weighting") <- weighting
    else
      stop("invalid weighting")
    x
  }
##  Modified command "TermDocumentMatrix" on package tm
##  and defined "TermDocumentMatrixCN"
TermDocumentMatrixCN<-
  function (x, control = list()) 
  {
    stopifnot(is.list(control))
    tflist <- lapply(unname(content(x)), termFreqCN, control)
    tflist <- lapply(tflist, function(y) y[y > 0])
    v <- unlist(tflist)
    i <- names(v)
    allTerms <- sort(unique(as.character(if (is.null(control$dictionary)) i else control$dictionary)))
    i <- match(i, allTerms)
    j <- rep(seq_along(x), sapply(tflist, length))
    docs <- as.character(meta(x, "id", "local"))
    if (length(docs) != length(x)) {
      warning("invalid document identifiers")
      docs <- NULL
    }
    m <- simple_triplet_matrix(i = i, j = j, v = as.numeric(v), 
                               nrow = length(allTerms), ncol = length(x), dimnames = list(Terms = allTerms, 
                                                                                          Docs = docs))
    bg <- control$bounds$global
    if (length(bg) == 2L && is.numeric(bg)) {
      rs <- row_sums(m > 0)
      m <- m[(rs >= bg[1]) & (rs <= bg[2]), ]
    }
    weighting <- control$weighting
    if (is.null(weighting)) 
      weighting <- weightTf
    .TermDocumentMatrix(m, weighting)
  }


#---------------------------------------------------------------------------------------------------------
geturl <- function( page_start, page_end, range,data ){

for( i in page_start:page_end){    # in後面的為網址後面的數字 用來判斷幾頁到第幾頁
  tmp <- paste(i, '.html', sep='')
  url <- paste('http://www.ptt.cc/bbs/Gossiping/index', tmp, sep='')
  url
  
  url<-GET(url, config=set_cookies("over18"="1"),encoding = 'UTF-8')      #   over18 = 1 是因為八卦版有18歲限制 如果沒有這樣
                                                                          #   會因為cookie的判斷 直接跳到要確認是否滿18歲的介面
  url.list<-c()  
 
   
  html <- htmlParse(url,encoding='UTF-8')
  temp.list <- xpathSApply(html, "//div[@class='title']/a[@href]", xmlAttrs) #暫存每篇文章網址

  
  
  Responsetime<-xpathSApply(html, "//div[@class='r-ent']", xmlValue)    #取每篇文章的回應數
  Responsetime
  
  for ( x in c(1:20))    #每頁有20篇文章 這邊要注意避開最新的那頁否則會出錯 因為最新的那頁不一定會滿20篇文章
  {
    k<-substr(Responsetime[x],5,8)   #k為回應數 但是是chr型別
    k<-gsub("\t","",k)
    k<-gsub("\n","",k)
    
    grepl("爆",k)
    num<-strtoi(k, base = 0L)    #num為每篇回應數
    if( is.na(num) )
      num<-0
    if(grepl("爆",k))
      num<-9999
    
    if( !is.na( num ) && (num > range) ) 
    {
     
      url.list[length(url.list)+1] <- temp.list[x]
        
    }
    
   
    #browser()
      
    
  }    

  #url.list <- xpathSApply(html, "//div[@class='title']/a[@href]", xmlAttrs)
  url.list
  data_ <- rbind(data, paste('www.ptt.cc', url.list, sep=''))
  #
  # x <- c(1, 2, 3)
  # y <- c(10, 20, 30)
  # rbind(x, y) 
  # [,1] [,2] [,3]
  # x    1    2    3
  # y   10   20   30
  
  #browser()
}
  
  eval.parent(substitute( data<-data_ )  )  

}
#-----------------------------------------------------------------------------------------------------
getdoc <- function(line){
  
  #ROC<-“<title>中華民國 – 維基百科，自由的百科全書</title>"
  #regexpr(“中華民國",ROC)
  #[1] 8
  
  start <- regexpr('www', line)[1]
  
  end <- regexpr('html', line)[1]
 
  
  if(start != -1 & end != -1){
    url <- substr(line, start, end+3)
    url<- paste( 'http://',url, sep='' )
   
    html <- GET(url, config=set_cookies("over18"="1"), encoding='UTF-8')
    
    html <- htmlParse(html,encoding='UTF-8')
  
    name<- xpathSApply( html, "//head/title", xmlValue)
 
    doc <- xpathSApply( html, "//div[@id='main-content']", xmlValue)
  
    name
    
    
    
    #name <- strsplit(url, '/')[[1]][6]    
    
    #gsub( 'html','txt', name)
    
    name = paste(name, '.txt', sep='')       #輸出成.txt檔
    name = str_replace_all( name, '\\<',"")  #檔名不允許有?號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\>',"")  #檔名不允許有?號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\?',"")  #檔名不允許有?號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\:',"")  #檔名不允許有:號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\：',"")  #檔名不允許有:號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\"',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\/',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\,',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\，',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\|',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    name = str_replace_all( name, '\\\\',"")  #檔名不允許有"號 但文章標題會有 如果直接拿文章標題當檔名 要將特殊字元去掉
    write(doc, name  )   
    #browser()
    
  }      
}


#------------------------------------------------------------------------------------------------ 
 remove_trash<- function(word)       
 {
   
   return (gsub("[A-Za-z0-9]", "", word))
   
 }
 
 #-----------------------------以上為收集資料---------------------------------------------------

text_mining<- function(name){      

 d.corpus <- Corpus( DirSource(name), list(language = NA))  # 利用tm的套件來讀取爬到的資料  "5月19~5月15"為資料夾名稱 要設定目前的工作目錄
 d.corpus <- tm_map(d.corpus, removePunctuation) #清除標點符號
 d.corpus <- tm_map(d.corpus, removeNumbers)    #清除數字
 d.corpus <- tm_map(d.corpus, remove_trash  )   #清楚一些英文字等等 a-z A-Z 0-9   remove為自定義函式
 #words <- readLines("ptt.scel")

 #installDict("C:/Users/user/Desktop/R final_project/ptt.scel","ptt",dicttype = "scel")   #新增ptt常用語進字典裡幫助斷詞
 #installDict("C:/Users/user/Desktop/R final_project/網路.scel","Internet",dicttype = "scel")
 #installDict("C:/Users/user/Desktop/R final_project/成語俗語.scel","idiom",dicttype = "scel")
 #installDict("C:/Users/user/Desktop/R final_project/aaaa.scel","ccc",dicttype = "scel")
 #installDict("C:/Users/user/Desktop/R final_project/2017-5.txt","2017",dicttype = "text")
 #listDict()                                                                              #查看目前有哪些字典
 
 #uninstallDict("ccc") #清空字典  


 #---------------------------------
 #segmentCN函數解釋
 #segmentCN(strwords,  
 #analyzer = get("Analyzer", envir = .RwordsegEnv),  
 #nature = FALSE, nosymbol = TRUE,  
 #returnType = c("vector", "tm"), isfast = FALSE,  
 #outfile = "", blocklines = 1000)  
 #strwords：中文句子
 #analyzer：分析的java對象
 #nature：是否識別詞組的詞性（動詞、形容詞）
 #nosymbol:是否保留句子符號
 #returnType：默認是一個字符串，也可以保存成其他的樣式，比如tm格式，以供tm包分析
 #isfast：“否”代表劃分成一個個字符，“是”代表保留句子，只是斷句
 #outfile：如果輸入是一個文件，文件的路徑是啥
 #blocklines：一行的最大讀入字符數
 #--------------------------------------
 
 
 d.corpus <- tm_map(d.corpus[1:length( d.corpus) ], segmentCN, nature = TRUE)  #解釋如上                        
 

 d.corpus <- tm_map(d.corpus, function(sentence) {                #只取名詞
   noun <- lapply(sentence, function(w) {
     w[names(w) == "n"]
   })
   unlist(noun)
 })
 d.corpus <- Corpus(VectorSource(d.corpus))
 
 inspect(d.corpus )
 
    #     append 可插入在原本字串後面                          停用字符就像是語助詞一樣:一直 可能 或許這類的詞皆為斷詞對資料分析沒幫助
 myStopWords <- c(stopwordsCN())  #因為每篇文章都一定會有這些字 而這些字對我們沒幫助
 myStopWords <- append( myStopWords, c("文章","網址","問題","八卦","政府","原因","結果","時候","新聞","標題","編輯", "時間", "發信", "實業", "作者","東西") )        
 myStopWords <- append( myStopWords,c("國家","媒體","高調","垃圾","法律","社會","感覺","父母","小孩","男子","女子","世界","事情","人家","記者","女生") )           #新增一些ptt文章標題常出現的字去除掉
 myStopWords <- append( myStopWords,c("討論","心得","面試","情報","問卷","聘書","徵才","請益","分析","公告") )
 d.corpus <- tm_map(d.corpus, removeWords, myStopWords) #去除斷詞
 #d.corpus
 
 #head(myStopWords, 50) #可看有哪些斷詞  50為前50筆
 tdm <- TermDocumentMatrixCN(d.corpus, control = list(wordLengths = c(2, Inf)))  #轉成矩陣 長度為2的才轉 這裡使用網友提供的
                                                                                 #而不是套件內的TermDocumentMatrix
 #str(d.corpus)
 #str(tdm)
 tdm
 inspect(tdm[1:20, 1:3])
 #inspect(d.corpus)
 
 
 
 m1 <- as.matrix(tdm)
 v <- sort(rowSums(m1), decreasing = TRUE)
 d <- data.frame(word = names(v), freq = v)
 
 wordcloud(d$word, d$freq, min.freq = 150, random.order = F, ordered.colors = F, 
           colors = rainbow(length(row.names(m1))))
 
 write.csv( v,"freq.csv")
 
}
 
 #--------------------------------main--------------------------------------------------------------------------------------
 data<- list()
 page_start<-as.integer(readline(prompt = "請輸入網址開頭如 https://www.ptt.cc/bbs/Gossiping/index23091.html 中的 23091: "))
 page_end<-as.integer(readline(prompt = "請輸入網址結尾:"))
 range<-as.integer(readline(prompt = "請輸入要抓的回應數要在多少以上的文章:"))
 
 setwd("C:/Users/user/Desktop/R final_project/new") #自行設定要存放檔案的資料夾
 
 geturl( page_start,page_end,range,data )
 sapply(data, getdoc)   #輸出
 
 setwd("C:/Users/user/Desktop/R final_project/") #自行設定存放檔案資料夾的上一層位置
 Foldername <- as.character(readline(prompt = "請輸入存放檔案資料夾的名稱:"))
 text_mining(Foldername)
 
 
 
 
 
 
 
 

