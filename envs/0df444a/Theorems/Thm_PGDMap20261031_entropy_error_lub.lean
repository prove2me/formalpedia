-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_error_lub
-- name    : PGDMap20261031.entropy_error_lub
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:59.929114+00:00
-- url     : https://prove2.me/theorems/a6fc9f59-5507-4453-90e3-611ea2efd0eb
-- title:
--   The curvature-error supremum is finite and well posed
-- statement:
--   ## Statement
--
--   A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $t$, let $C_M(t)=\sum_{j=0}^{m-1}w_j a_j/(1-a_jt^2)$ and $D_M(t)=\lambda/(1-t^2)$; for real $c,p,t$, let $e_{M,c,p}(t)=\big(pQ_c(t)-C_M(t)\big)/\big(pQ_c(t)+D_M(t)\big)$, with total real division. Let $E_M(c,p)=\{|e_{M,c,p}(t)|:0\le t<1\}$ and $r_M(c,p)=\operatorname{sSup}_{\mathbb R}E_M(c,p)$, the total real supremum operation, which uses its library default on an empty or unbounded-above set. A pair $(c,p)\in\mathbb R^2$ is admissible exactly when $0\le c\le2$ and $p>0$. The theorem asserts the following. For every mixture $M$ and every admissible real pair $(c,p)$, $r_M(c,p)$ is a least upper bound of $E_M(c,p)$: every $|e_{M,c,p}(t)|$ with $0\le t<1$ is at most $r_M(c,p)$, and $r_M(c,p)$ is at most every real upper bound of all these values.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, definitions p. 1; Lemma 1 and Theorem 1 proof pp. 2-4; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_error_lub : ErrorProfileLUBClaim := by sorry
