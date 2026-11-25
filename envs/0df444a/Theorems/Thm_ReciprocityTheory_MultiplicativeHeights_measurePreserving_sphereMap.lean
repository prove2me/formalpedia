-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_sphereMap
-- name    : ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:35.31004+00:00
-- url     : https://prove2.me/theorems/f9a0e05b-13bd-45d6-96c0-1155009c37c4
-- title:
--   Multiplicative Heights: measure Preserving sphere Map
-- statement:
--   The Multiplicative Heights construction uses the measure Preserving sphere Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L46-L51

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

theorem ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (sphereMap U) (sphereProb n) (sphereProb n) := by sorry
