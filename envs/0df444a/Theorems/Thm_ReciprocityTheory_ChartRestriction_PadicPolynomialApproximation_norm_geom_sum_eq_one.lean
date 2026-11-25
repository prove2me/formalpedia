-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_geom_sum_eq_one
-- name    : ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:35.640798+00:00
-- url     : https://prove2.me/theorems/48d47e6a-98b9-4515-9fb3-b1c5b74ec14f
-- title:
--   Padic Polynomial Approximation: norm geom sum eq one
-- statement:
--   The Padic Polynomial Approximation construction uses the norm geom sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L57-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by sorry
