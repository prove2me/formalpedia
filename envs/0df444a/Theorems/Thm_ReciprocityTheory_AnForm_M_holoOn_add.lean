-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_add
-- name    : ReciprocityTheory.AnForm.M.holoOn_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:03.636483+00:00
-- url     : https://prove2.me/theorems/f0f2f600-6dbd-5acb-a93d-da3ab233c38e
-- title:
--   M: holo On add
-- statement:
--   The M construction uses the holo On add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L39-L42

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

theorem ReciprocityTheory.AnForm.M.holoOn_add (A : FinHolAtlas e X) {W₁ W₂ : Set X} {G₁ G₂ : X → ℂ}
    (h₁ : A.HoloOn W₁ G₁) (h₂ : A.HoloOn W₂ G₂) :
    A.HoloOn (W₁ ∩ W₂) (fun z => G₁ z + G₂ z) := by sorry
