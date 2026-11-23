-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
-- name    : P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:38.57908+00:00
-- url     : https://prove2.me/theorems/9cb67d63-d72e-452b-9747-6aa5e0779eb1
-- title:
--   P2 M Reciprocity Theory Chart Restriction Padic Polynomial Approximation norm eq of norm sub lt  a47ddde60030: P2 M Reciprocity Theory Chart Restriction Padic Polynomial Approximation norm eq of norm
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction Padic Polynomial Approximation norm eq of norm sub lt  a47ddde60030 construction uses the P2 M Reciprocity Theory Chart Restriction Padic Polynomial Approximation norm eq of norm sub lt  a47ddde60030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormEqOfNormSubLt.lean#L11-L13

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

theorem P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030 {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«PadicPolynomialApproximation».«norm_eq_of_norm_sub_lt'» := P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
