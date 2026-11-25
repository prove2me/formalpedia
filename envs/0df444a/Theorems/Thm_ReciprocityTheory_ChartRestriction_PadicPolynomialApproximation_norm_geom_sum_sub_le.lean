-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_geom_sum_sub_le
-- name    : ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_sub_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:07.710704+00:00
-- url     : https://prove2.me/theorems/ca439149-ddf6-4d68-adf5-df95b6feead9
-- title:
--   Padic Polynomial Approximation: norm geom sum sub le
-- statement:
--   The Padic Polynomial Approximation construction uses the norm geom sum sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L46-L55

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

theorem ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_sub_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by sorry
