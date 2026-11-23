-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:22.430854+00:00
-- url     : https://prove2.me/theorems/8ebcdf98-5392-42c0-84d5-e9cda12f4a15
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA is Open omega  0bdf6ae9539d: P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA is Open omega  0bdf6ae9539d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA is Open omega  0bdf6ae9539d construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA is Open omega  0bdf6ae9539d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiM.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiM.lean#L60-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d : IsOpen (OmegaSet n) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«InfKA».«isOpen_omega'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d
