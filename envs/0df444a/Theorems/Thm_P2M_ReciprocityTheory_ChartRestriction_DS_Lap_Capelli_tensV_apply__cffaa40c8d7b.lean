-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:16.212867+00:00
-- url     : https://prove2.me/theorems/8e5dadbc-f8d2-41a6-9916-d04992e3a8c8
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens V apply  cffaa40c8d7b: P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens V apply  cffaa40c8d7b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens V apply  cffaa40c8d7b construction uses the P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens V apply  cffaa40c8d7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L13-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M)
    (e : Fin n) : tensV E a b f e = E a b (f e) + if e = a then f b else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Lap».«Capelli».«tensV_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b
