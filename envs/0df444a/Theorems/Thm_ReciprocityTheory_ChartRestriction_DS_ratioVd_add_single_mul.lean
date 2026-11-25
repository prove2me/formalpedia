-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ratioVd_add_single_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.ratioVd_add_single_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:32.164798+00:00
-- url     : https://prove2.me/theorems/dab4bd95-44f8-5398-b56e-5f7d39db5fd2
-- title:
--   DS: ratio Vd add single mul
-- statement:
--   The DS construction uses the ratio Vd add single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L219-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L219-L235

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.ratioVd_add_single_mul {μ : Fin n → ℝ} (s : Fin n) (hμ : Function.Injective μ)
    (hμs : Function.Injective (μ + Pi.single s 1)) :
    ratioVd (μ + Pi.single s 1) s * ratioV μ s = 1 := by sorry
