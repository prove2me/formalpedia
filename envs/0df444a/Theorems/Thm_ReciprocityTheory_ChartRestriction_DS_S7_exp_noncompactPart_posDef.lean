-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exp_noncompactPart_posDef
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:15.217807+00:00
-- url     : https://prove2.me/theorems/174ee8d7-5740-405c-9fa0-3f3cbf975a89
-- title:
--   S7: exp noncompact Part pos Def
-- statement:
--   The S7 construction uses the exp noncompact Part pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L161-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L161-L172

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : (NormedSpace.exp X).PosDef := by sorry
