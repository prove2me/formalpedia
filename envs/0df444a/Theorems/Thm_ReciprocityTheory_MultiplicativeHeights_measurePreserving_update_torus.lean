-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_update_torus
-- name    : ReciprocityTheory.MultiplicativeHeights.measurePreserving_update_torus
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:17.743807+00:00
-- url     : https://prove2.me/theorems/6eeb6d3d-6d1f-5978-861b-c88d72ae2b59
-- title:
--   Multiplicative Heights: measure Preserving update torus
-- statement:
--   The Multiplicative Heights construction uses the measure Preserving update torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L71-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L71-L101

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.measurePreserving_update_torus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (torusProb ι) := by sorry
