-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_sphereMap
-- name    : ReciprocityTheory.MultiplicativeHeights.continuous_sphereMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:35.870815+00:00
-- url     : https://prove2.me/theorems/1200245a-e6b0-4b75-bf21-b1f5284182ad
-- title:
--   Multiplicative Heights: continuous sphere Map
-- statement:
--   The Multiplicative Heights construction uses the continuous sphere Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L15-L18

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

theorem ReciprocityTheory.MultiplicativeHeights.continuous_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Continuous (sphereMap U) := by sorry
