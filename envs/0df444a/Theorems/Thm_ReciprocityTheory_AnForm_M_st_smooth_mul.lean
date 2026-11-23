-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_mul
-- name    : ReciprocityTheory.AnForm.M.st_smooth_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:10.260359+00:00
-- url     : https://prove2.me/theorems/040bfab9-2970-40a9-95fd-7e8be275978c
-- title:
--   M: st smooth mul
-- statement:
--   The M construction uses the st smooth mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L28-L29

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

theorem ReciprocityTheory.AnForm.M.st_smooth_mul (A : FinHolAtlas e X) {f g : X → ℝ} (hf : A.Smooth f) (hg : A.Smooth g) :
    A.Smooth (fun x => f x * g x) := by sorry
