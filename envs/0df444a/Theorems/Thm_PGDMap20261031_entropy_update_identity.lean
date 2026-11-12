-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_update_identity
-- name    : PGDMap20261031.entropy_update_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:00.711075+00:00
-- url     : https://prove2.me/theorems/bbb22021-b84b-48ae-b3fe-c8e35e62f861
-- title:
--   The Bregman update yields both gradient-difference identities
-- statement:
--   ## Statement
--
--   A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For every real $t$, write $U(t)=\big(\log(1+t)-\log(1-t)\big)/2$, using the total real logarithm of the code. Define $S_M(t)=\sum_{j=0}^{m-1}w_j\sqrt{a_j}\,U(\sqrt{a_j}\,t)$ for real $t$. For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $c,t$, define $h_c(t)=\int_0^t Q_c(s)\,ds$, the oriented interval integral with respect to Lebesgue measure. For every such mixture $M$ and every real $c,p,\ell,x,y$, if $p h_c(y)+\lambda U(y)=p h_c(x)-S_M(x)-\ell$, then both $S_M(x)+\lambda U(x)+\ell=p\big(h_c(x)-h_c(y)\big)+\lambda\big(U(x)-U(y)\big)$ and $S_M(y)+\lambda U(y)+\ell=p\big(h_c(x)-h_c(y)\big)-\big(S_M(x)-S_M(y)\big)$ hold. There is no admissibility condition on $c,p$, no condition $-1<x,y<1$, and no nonzero-gradient assumption.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Lemma 1 proof, p. 2; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_update_identity : ∀ (M : EntropyMixture) (c p ell x y : ℝ),
    p * geometrySlope c y + M.lambda * artanh y =
      p * geometrySlope c x - mixtureSlope M x - ell →
    (mixtureSlope M x + M.lambda * artanh x + ell =
      p * (geometrySlope c x - geometrySlope c y) + M.lambda * (artanh x - artanh y)) ∧
    (mixtureSlope M y + M.lambda * artanh y + ell =
      p * (geometrySlope c x - geometrySlope c y) - (mixtureSlope M x - mixtureSlope M y)) := by sorry
