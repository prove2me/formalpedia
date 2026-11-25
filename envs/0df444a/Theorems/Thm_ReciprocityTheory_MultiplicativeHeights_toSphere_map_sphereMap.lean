-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_toSphere_map_sphereMap
-- name    : ReciprocityTheory.MultiplicativeHeights.toSphere_map_sphereMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:58.047866+00:00
-- url     : https://prove2.me/theorems/bde7806d-f151-4f37-881f-7dd69ca6875f
-- title:
--   Multiplicative Heights: to Sphere map sphere Map
-- statement:
--   The Multiplicative Heights construction uses the to Sphere map sphere Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L20-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L20-L44

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
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

theorem ReciprocityTheory.MultiplicativeHeights.toSphere_map_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Measure.map (sphereMap U) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by sorry
