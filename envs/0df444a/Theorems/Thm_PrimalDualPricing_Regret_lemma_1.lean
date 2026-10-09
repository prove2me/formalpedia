-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_1
-- name    : PrimalDualPricing.Regret.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:46.662985+00:00
-- url     : https://prove2.me/theorems/13d83982-4ed8-4cca-8cac-758beb93291d
-- title:
--   Lemma 1, p. 14 — for $n\ge3$ the number of phases satisfies $K\le3\log n+3$
-- statement:
--   Let $\epsilon>0$ and $n\ge3$. The number of phases of Algorithm 1,
--   $$K=\min\big\{k\ge1:(\bar\Delta^{(k)})^2\le n^{-1/2}(\log n)^{2+16\epsilon}\big\},\qquad \bar\Delta^{(k)}=n^{-\frac14(1-(3/5)^{k-1})},$$
--   satisfies
--   $$K\le3\log n+3.$$
--
--   The number of phases enters every union bound of the analysis, so this bound keeps them polynomial in $\log n$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 14, Lemma 1 (parameters p. 13)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Params

namespace PrimalDualPricing.Regret

/-- Lemma 1 (Chen–Gallego, arXiv:1812.09234v3, p. 14). For every `ε > 0` and `n ≥ 3`, the total number of
phases `K = min{k ≥ 1 : (Δ̄^{(k)})² ≤ n^{−1/2}(log n)^{2+16ε}}` of Algorithm 1 satisfies `K ≤ 3 log n + 3`. -/
theorem lemma_1 (eps : ℝ) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) :
    (numPhases eps n : ℝ) ≤ 3 * Real.log n + 3 := by sorry

end PrimalDualPricing.Regret
