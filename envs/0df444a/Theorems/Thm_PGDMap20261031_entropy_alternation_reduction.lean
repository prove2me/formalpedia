-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_alternation_reduction
-- name    : PGDMap20261031.entropy_alternation_reduction
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:57.69178+00:00
-- url     : https://prove2.me/theorems/53420768-f1c6-4634-9e16-6075d4bbea90
-- title:
--   Lemma 2: three alternating contacts certify global optimality
-- statement:
--   ## Statement
--
--   For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For real $t$, let $C_M(t)=\sum_{j=0}^{m-1}w_j a_j/(1-a_jt^2)$ and $D_M(t)=\lambda/(1-t^2)$; for real $c,p,t$, let $e_{M,c,p}(t)=\big(pQ_c(t)-C_M(t)\big)/\big(pQ_c(t)+D_M(t)\big)$, with total real division. Let $E_M(c,p)=\{|e_{M,c,p}(t)|:0\le t<1\}$ and $r_M(c,p)=\operatorname{sSup}_{\mathbb R}E_M(c,p)$, the total real supremum operation, which uses its library default on an empty or unbounded-above set. A pair $(c,p)\in\mathbb R^2$ is admissible exactly when $0\le c\le2$ and $p>0$. A pair $z=(c,p)$ is an optimum for $M$ exactly when it is admissible and $r_M(c,p)\le r_M(d,q)$ for every admissible pair $(d,q)$. Assume the following assertions with their full universal quantification: For every real $c_1,c_2$ with $0\le c_1<c_2\le2$, and every pair of real numbers $s,t$ with $0\le s<t<1$, $Q_{c_2}(s)/Q_{c_1}(s)<Q_{c_2}(t)/Q_{c_1}(t)$. Under these assumptions, the theorem concludes the following assertion with its full universal quantification: For every mixture $M$, all real $c,p,b$ with $(c,p)$ admissible and $b>0$, if $|e_{M,c,p}(t)|\le b$ for every $0\le t<1$ and there exist real $t_1,t_2,t_3,\sigma$ with $0\le t_1<t_2<t_3<1$, $\sigma\in\{1,-1\}$, and $e_{M,c,p}(t_1)=\sigma b$, $e_{M,c,p}(t_2)=-\sigma b$, $e_{M,c,p}(t_3)=\sigma b$, then $(c,p)$ is an optimum for $M$, $r_M(c,p)=b$, and every real pair $z$ that is an optimum for $M$ equals $(c,p)$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Lemma 2, pp. 2-3; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_alternation_reduction : PowerSingleCrossingClaim → AlternationCertificateClaim := by sorry
