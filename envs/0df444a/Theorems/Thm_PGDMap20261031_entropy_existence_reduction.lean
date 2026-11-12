-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_existence_reduction
-- name    : PGDMap20261031.entropy_existence_reduction
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:03.308789+00:00
-- url     : https://prove2.me/theorems/c372f079-2cc6-4653-8465-2f06266f34f5
-- title:
--   Compactness, boundary exclusion, and location of the optimum
-- statement:
--   ## Statement
--
--   For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $a,c,u$, put $T_{a,c}(u)=(1-au)Q_c(\sqrt u)$ and $\tau(a)=(\sqrt{1+8a}-1)/2$, with the total real square root. A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For real $t$, let $C_M(t)=\sum_{j=0}^{m-1}w_j a_j/(1-a_jt^2)$ and $D_M(t)=\lambda/(1-t^2)$; for real $c,p,t$, let $e_{M,c,p}(t)=\big(pQ_c(t)-C_M(t)\big)/\big(pQ_c(t)+D_M(t)\big)$, with total real division. Let $E_M(c,p)=\{|e_{M,c,p}(t)|:0\le t<1\}$ and $r_M(c,p)=\operatorname{sSup}_{\mathbb R}E_M(c,p)$, the total real supremum operation, which uses its library default on an empty or unbounded-above set. A pair $(c,p)\in\mathbb R^2$ is admissible exactly when $0\le c\le2$ and $p>0$. A pair $z=(c,p)$ is an optimum for $M$ exactly when it is admissible and $r_M(c,p)\le r_M(d,q)$ for every admissible pair $(d,q)$. Let $B_0(M)=\sum_{j=0}^{m-1}w_j a_j$, $B_1(M)=\sum_{j=0}^{m-1}w_j a_j/(1-a_j)$, $a_{\max}(M)=\operatorname{sSup}_{\mathbb R}\{a_j:0\le j<m\}$, $\tau(a)=(\sqrt{1+8a}-1)/2$ for real $a$, and $\beta(M)=B_0(M)/(B_0(M)+2\lambda)$; the supremum defining $a_{\max}(M)$ is over a nonempty finite set. Assume the following assertions with their full universal quantification: For every real $a,c$ with $0<a<1$ and $0<c<1$, both of the following implications hold: if $\tau(a)\le c$, then $T_{a,c}(s)<T_{a,c}(t)$ for every $0\le s<t<1$; if $c<\tau(a)$, then there is a real $u$ with $0<u<1$ such that $T_{a,c}(t)<T_{a,c}(s)$ whenever $0\le s<t\le u$, and $T_{a,c}(s)<T_{a,c}(t)$ whenever $u\le s<t<1$; and For every mixture $M$ and every real pair $z=(c,p)$ that is an optimum for $M$, $|e_{M,c,p}(t)|\le r_M(c,p)$ for all $0\le t<1$, and there exist real $t_1,t_2,t_3,\sigma$ with $0\le t_1<t_2<t_3<1$, $\sigma\in\{1,-1\}$, and $e_{M,c,p}(t_1)=\sigma r_M(c,p)$, $e_{M,c,p}(t_2)=-\sigma r_M(c,p)$, $e_{M,c,p}(t_3)=\sigma r_M(c,p)$. Under these assumptions, the theorem concludes the following assertion with its full universal quantification: For every mixture $M$, there exists a real pair $z=(c,p)$ which is an optimum for $M$ and satisfies $0<c<\tau(a_{\max}(M))<1$, $B_0(M)/2<p<B_1(M)$, and $0<r_M(c,p)<\beta(M)<1$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Theorem 1 proof, pp. 3-5; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_existence_reduction : PowerThresholdClaim → NecessaryAlternationClaim → LocatedExistenceClaim := by sorry
