-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_sum
-- name    : ReciprocityTheory.AnForm.M.PLAux.smooth_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:36.146887+00:00
-- url     : https://prove2.me/theorems/8e28fa30-9dd9-4007-8eb9-cc1da88dd17c
-- title:
--   PLAux: smooth sum
-- statement:
--   The PLAux construction uses the smooth sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L28-L30

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.smooth_sum {A : FinHolAtlas e X} {ι : Type} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, A.Smooth (f i)) : A.Smooth (fun x => ∑ i ∈ s, f i x) := by sorry
