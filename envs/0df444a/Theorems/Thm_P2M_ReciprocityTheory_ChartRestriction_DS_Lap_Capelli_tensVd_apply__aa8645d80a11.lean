-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensVd_apply__aa8645d80a11
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensVd_apply__aa8645d80a11
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:42.275978+00:00
-- url     : https://prove2.me/theorems/0e9dcc29-cd32-4cf7-87d5-46212e3467a2
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens Vd apply  aa8645d80a11: P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens Vd apply  aa8645d80a11
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens Vd apply  aa8645d80a11 construction uses the P2 M Reciprocity Theory Chart Restriction DS Lap Capelli tens Vd apply  aa8645d80a11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L18-L21

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensVd_apply__aa8645d80a11 {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M)
    (e : Fin n) : tensVd E a b f e = E a b (f e) - if e = b then f a else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Lap».«Capelli».«tensVd_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensVd_apply__aa8645d80a11
