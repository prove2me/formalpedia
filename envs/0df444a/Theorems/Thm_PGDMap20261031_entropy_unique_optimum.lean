-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_unique_optimum
-- name    : PGDMap20261031.entropy_unique_optimum
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:01.35345+00:00
-- url     : https://prove2.me/theorems/762e37b9-3d71-48d7-966f-1f9954a52044
-- title:
--   Uniqueness and strict location of the jointly optimal geometry
-- statement:
--   ## Statement
--
--   A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $t$, let $C_M(t)=\sum_{j=0}^{m-1}w_j a_j/(1-a_jt^2)$ and $D_M(t)=\lambda/(1-t^2)$; for real $c,p,t$, let $e_{M,c,p}(t)=\big(pQ_c(t)-C_M(t)\big)/\big(pQ_c(t)+D_M(t)\big)$, with total real division. Let $E_M(c,p)=\{|e_{M,c,p}(t)|:0\le t<1\}$ and $r_M(c,p)=\operatorname{sSup}_{\mathbb R}E_M(c,p)$, the total real supremum operation, which uses its library default on an empty or unbounded-above set. A pair $(c,p)\in\mathbb R^2$ is admissible exactly when $0\le c\le2$ and $p>0$. A pair $z=(c,p)$ is an optimum for $M$ exactly when it is admissible and $r_M(c,p)\le r_M(d,q)$ for every admissible pair $(d,q)$. Let $B_0(M)=\sum_{j=0}^{m-1}w_j a_j$, $B_1(M)=\sum_{j=0}^{m-1}w_j a_j/(1-a_j)$, $a_{\max}(M)=\operatorname{sSup}_{\mathbb R}\{a_j:0\le j<m\}$, $\tau(a)=(\sqrt{1+8a}-1)/2$ for real $a$, and $\beta(M)=B_0(M)/(B_0(M)+2\lambda)$; the supremum defining $a_{\max}(M)$ is over a nonempty finite set. The theorem asserts the following. For every mixture $M$, there exists exactly one real pair $z$ that is an optimum for $M$, and every such optimum $z=(c,p)$ satisfies $0<c<\tau(a_{\max}(M))<1$, $B_0(M)/2<p<B_1(M)$, and $0<r_M(c,p)<\beta(M)<1$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Theorem 1(2)-(3), p. 2; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_unique_optimum : UniqueLocatedOptimumClaim := by sorry
