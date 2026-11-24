-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_8
-- name    : ShockWear.Inherit.Supplement.theorem32_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:58:53.054555+00:00
-- url     : https://prove2.me/theorems/f9dd02ce-4cbc-4210-a7c9-b94b09dd313c
-- title:
--   Theorem 3.2(3.8) — increasing successive ratios of shock survival probabilities give DHR
-- statement:
--   Let shocks arrive at rate $\lambda>0$, let $1\geq\bar P_0\geq\bar P_1\geq\cdots\geq0$ be the probabilities of surviving the first $k$ shocks, and let $\bar H(t)=\sum_{k\ge0}\bar P_k e^{-\lambda t}(\lambda t)^k/k!$ for $t\ge0$. If the successive ratios $\bar P_k/\bar P_{k-1}$ are increasing in $k=1,2,\dots$, that is,
--   $$\bar P_{j+1}\bar P_k\leq\bar P_{k+1}\bar P_j\qquad(0\le j\le k),$$
--   then $H$ has decreasing hazard rate: for every $x>0$ and $0\leq s\leq t$,
--   $$\bar H(x+s)\,\bar H(t)\leq\bar H(x+t)\,\bar H(s).$$
--
--   This is the DHR companion of Theorem 3.1 (3.2): the reversed discrete condition gives the reversed ageing property.
--
--   **Formalization Note** Unlike Theorem 3.1, the paper allows $\bar P_0<1$, i.e. an atom $1-\bar P_0$ at the origin; therefore DHR is stated on the life-distribution domain $t\geq0$ (the ratio $\bar H(x+t)/\bar H(t)$ jumps down at $0$ when $\bar P_0<1$, because $\bar H=1$ on $t<0$). "Increasing" is weak, and the ratio conditions are cross-multiplied so that zero survival probabilities need no division.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.8), with definition (ii′), p. 632; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

/-- Theorem 3.2(3.8): increasing successive ratios of the shock survival
probabilities give a DHR life law (an atom at the origin is allowed). -/
theorem theorem32_8 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hinc : ∀ j k, j ≤ k → P (j + 1) * P k ≤ P (k + 1) * P j) :
    IsDHR (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
