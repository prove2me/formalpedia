-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_mul
-- name    : ReciprocityTheory.AnForm.M.holoOn_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:19.583315+00:00
-- url     : https://prove2.me/theorems/d98f1c34-2797-4177-8cb0-1da467b25898
-- title:
--   M: holo On mul
-- statement:
--   The M construction uses the holo On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L44-L45

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
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

theorem ReciprocityTheory.AnForm.M.holoOn_mul (A : FinHolAtlas e X) {W : Set X} {G : X → ℂ} (h : A.HoloOn W G) (c : ℂ) :
    A.HoloOn W (fun z => c * G z) := by sorry
