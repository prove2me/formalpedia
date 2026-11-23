-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:41.05754+00:00
-- url     : https://prove2.me/theorems/a03315c0-8c80-425a-ba34-e16867c4c56d
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 is Hermitian of mem noncompact Part  f516412af8b5: P2 M Reciprocity Theory Chart Restriction DS S7 is Hermitian of mem noncompact Part  f516412af8b5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 is Hermitian of mem noncompact Part  f516412af8b5 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 is Hermitian of mem noncompact Part  f516412af8b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L36-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
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
variable {ε : Fin n → Bool}
open PolarDecomposition

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5 {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«isHermitian_of_mem_noncompactPart'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5
