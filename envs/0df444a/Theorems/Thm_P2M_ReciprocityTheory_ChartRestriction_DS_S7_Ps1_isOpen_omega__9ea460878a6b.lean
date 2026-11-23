-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:46.514803+00:00
-- url     : https://prove2.me/theorems/70617992-a62b-4a61-a0e2-4e96fa6031d5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Ps1 is Open omega  9ea460878a6b: P2 M Reciprocity Theory Chart Restriction DS S7 Ps1 is Open omega  9ea460878a6b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Ps1 is Open omega  9ea460878a6b construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Ps1 is Open omega  9ea460878a6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L54-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
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
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b : IsOpen (OmegaSet n) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«Ps1».«isOpen_omega'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b
