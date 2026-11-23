-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_sum
-- name    : ReciprocityTheory.AnForm.M.st_smooth_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:45.439247+00:00
-- url     : https://prove2.me/theorems/918b2d59-d0b9-4349-bc10-9792ac212ea3
-- title:
--   M: st smooth sum
-- statement:
--   The M construction uses the st smooth sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L33-L34

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_smooth_sum (A : FinHolAtlas e X) {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ m, A.Smooth (f m)) : A.Smooth (fun x => ∑ m ∈ s, f m x) := by sorry
