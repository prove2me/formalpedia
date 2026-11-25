-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_hasSum_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.coefC_hasSum_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:01.035987+00:00
-- url     : https://prove2.me/theorems/dc9f0167-4880-5dff-b0d0-d06b2d0f0a1d
-- title:
--   DS: coef C has Sum mul
-- statement:
--   The DS construction uses the coef C has Sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L66-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
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

theorem ReciprocityTheory.ChartRestriction.DS.coefC_hasSum_mul {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by sorry
