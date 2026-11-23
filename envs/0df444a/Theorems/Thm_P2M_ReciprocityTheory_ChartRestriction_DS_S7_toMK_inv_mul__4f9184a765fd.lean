-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv_mul__4f9184a765fd
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv_mul__4f9184a765fd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:40.30508+00:00
-- url     : https://prove2.me/theorems/6daab6c4-c49f-4de8-b47e-5a20335e3d4a
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 to MK inv mul  4f9184a765fd: P2 M Reciprocity Theory Chart Restriction DS S7 to MK inv mul  4f9184a765fd
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 to MK inv mul  4f9184a765fd construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 to MK inv mul  4f9184a765fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L36-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv_mul__4f9184a765fd (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«toMK_inv_mul'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv_mul__4f9184a765fd
