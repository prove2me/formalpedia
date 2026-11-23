-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:46.512214+00:00
-- url     : https://prove2.me/theorems/2fa5d26a-638b-4cb8-99d9-afe42183217e
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Lap Capelli ee Vd apply  ec28e3696ecf: P2 M Reciprocity Theory Chart Restriction DS Lap Capelli ee Vd apply  ec28e3696ecf
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Lap Capelli ee Vd apply  ec28e3696ecf construction uses the P2 M Reciprocity Theory Chart Restriction DS Lap Capelli ee Vd apply  ec28e3696ecf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L27-L29

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (a : Fin n) :
    eeVd E f a = -∑ c, E a c (f c) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Lap».«Capelli».«eeVd_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf
