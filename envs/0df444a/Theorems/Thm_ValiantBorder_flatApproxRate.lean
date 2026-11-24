-- Prove2me | Theorems.Thm_ValiantBorder_flatApproxRate
-- name    : ValiantBorder.flatApproxRate
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:23:34.603931+00:00
-- url     : https://prove2.me/theorems/fe34f8bb-2edf-49f8-91af-6ca79baefbda
-- title:
--   Circuit lower bound in the flat case
-- statement:
--   For a fixed grid projection factor $κ$, there is a common size threshold for all flat fields and all polynomial families grid-complete with that factor. Beyond the threshold every Laurent-series approximating circuit has more than $2^{(\log_2 m)^{4/3}/1600^2}$ gates.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L229-L239).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L229-L239.

import Definitions.Def_ValiantBorder_fieldCases
import Definitions.Def_ValiantBorder_gridComplete
import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.flatApproxRate (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Paper.Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, ValiantBorder.GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Statement.Approximates (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by sorry
