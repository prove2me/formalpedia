-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_anti_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.fockT_anti_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:27.197916+00:00
-- url     : https://prove2.me/theorems/0c600345-b2ae-5acf-849e-21926d6d7e49
-- title:
--   DS: fock T anti sum
-- statement:
--   The DS construction uses the fock T anti sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L66-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.fockT_anti_sum {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by sorry
