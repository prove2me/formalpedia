-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_mIntConstPot
-- name    : ReciprocityTheory.AnForm.M.st_mIntConstPot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:56.653254+00:00
-- url     : https://prove2.me/theorems/fddaae99-0674-4c74-8ed0-d16446ea9cd8
-- title:
--   M: st m Int Const Pot
-- statement:
--   The M construction uses the st m Int Const Pot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L82-L93

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

theorem ReciprocityTheory.AnForm.M.st_mIntConstPot (A : FinHolAtlas (e + 1) X) (c : ℝ) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0 := by sorry
