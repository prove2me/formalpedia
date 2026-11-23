-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:02.539434+00:00
-- url     : https://prove2.me/theorems/5a5769e5-99be-4abb-aa38-add0e9029157
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA continuous to MK  342259628be7: P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA continuous to MK  342259628be7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA continuous to MK  342259628be7 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 Inf KA continuous to MK  342259628be7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiM.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiM.lean#L76-L82

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7 : Continuous fun k : KG ε => toMK k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«InfKA».«continuous_toMK'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7
