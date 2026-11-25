-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_hw_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.ePow_hw_lower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:47.037306+00:00
-- url     : https://prove2.me/theorems/0ae5bd59-54a3-5850-bf3f-525ab55341ae
-- title:
--   DS: e Pow hw lower
-- statement:
--   The DS construction uses the e Pow hw lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean#L22-L38

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

theorem ReciprocityTheory.ChartRestriction.DS.ePow_hw_lower {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (s r : Fin n) (hsr : s < r) : ePow E k s r v = 0 := by sorry
