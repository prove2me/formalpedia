-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:20.116154+00:00
-- url     : https://prove2.me/theorems/dacd7e8b-2b43-4ef5-b8fd-2d9f7c211db8
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul inv  47a4d626f289: P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul inv  47a4d626f289
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul inv  47a4d626f289 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul inv  47a4d626f289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L34-L34

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289 (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«toMK_mul_inv'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289
