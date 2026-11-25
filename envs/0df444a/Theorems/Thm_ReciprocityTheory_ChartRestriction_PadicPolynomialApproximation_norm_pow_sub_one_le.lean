-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_pow_sub_one_le
-- name    : ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_pow_sub_one_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:06.205832+00:00
-- url     : https://prove2.me/theorems/ee6e2cae-b609-4bfc-b45d-3f1781186340
-- title:
--   Padic Polynomial Approximation: norm pow sub one le
-- statement:
--   The Padic Polynomial Approximation construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L36-L44

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

theorem ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_pow_sub_one_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) : ‖y ^ k - 1‖ ≤ ‖y - 1‖ := by sorry
