-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:09.369037+00:00
-- url     : https://prove2.me/theorems/d04be762-4b12-4041-9007-cacdc024a991
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul  88ef2175972f: P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul  88ef2175972f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul  88ef2175972f construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 to MK mul  88ef2175972f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ToMKMulInv.lean#L20-L20

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«toMK_mul'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f
