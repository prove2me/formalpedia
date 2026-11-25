-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_toSphere_isometry
-- name    : ReciprocityTheory.MultiplicativeHeights.measurePreserving_toSphere_isometry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:27.673276+00:00
-- url     : https://prove2.me/theorems/7bc6ca5a-1625-5f1a-bbbf-ec342c8a843d
-- title:
--   Multiplicative Heights: measure Preserving to Sphere isometry
-- statement:
--   The Multiplicative Heights construction uses the measure Preserving to Sphere isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L57-L68

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
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
open MeasureTheory Metric
open scoped Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.measurePreserving_toSphere_isometry {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by sorry
