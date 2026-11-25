-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inv_one_sub_C_mul_X
-- name    : ReciprocityTheory.ChartRestriction.DS.inv_one_sub_C_mul_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:16.424796+00:00
-- url     : https://prove2.me/theorems/042b5965-2272-5950-a440-6dc781ed904a
-- title:
--   DS: inv one sub C mul X
-- statement:
--   The DS construction uses the inv one sub C mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L80-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L80-L91

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

theorem ReciprocityTheory.ChartRestriction.DS.inv_one_sub_C_mul_X (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X)⁻¹ = PowerSeries.mk (fun k => c ^ k) := by sorry
