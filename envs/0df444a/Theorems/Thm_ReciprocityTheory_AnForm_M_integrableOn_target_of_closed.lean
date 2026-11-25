-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_target_of_closed
-- name    : ReciprocityTheory.AnForm.M.integrableOn_target_of_closed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:49.122794+00:00
-- url     : https://prove2.me/theorems/09c7c5b1-779b-41ae-9508-43f23aa82b19
-- title:
--   M: integrable On target of closed
-- statement:
--   The M construction uses the integrable On target of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L57-L62

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem ReciprocityTheory.AnForm.M.integrableOn_target_of_closed {e : ℕ} {X : Type} [TopologicalSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} {G : (Fin e → ℂ) → ℝ}
    (hG0 : ∀ y ∈ ch.target, ch.symm y ∉ Z → G y = 0) (hG : IntegrableOn G (ch '' Z)) :
    IntegrableOn G ch.target := by sorry
