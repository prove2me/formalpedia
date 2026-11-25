-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfand_hw
-- name    : ReciprocityTheory.ChartRestriction.DS.gelfand_hw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:57.276504+00:00
-- url     : https://prove2.me/theorems/fa27bff5-9002-4053-bf49-50ab26a2d781
-- title:
--   DS: gelfand hw
-- statement:
--   The DS construction uses the gelfand hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L74-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.gelfand_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) : gelfand E k v = gval (icShift (ν + rho n)) k • v := by sorry
