-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_sphereRot
-- name    : ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereRot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:16.580902+00:00
-- url     : https://prove2.me/theorems/4376517c-886b-5ffc-b9fb-782b9c81ab7c
-- title:
--   Multiplicative Heights: measure Preserving sphere Rot
-- statement:
--   The Multiplicative Heights construction uses the measure Preserving sphere Rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L88-L91

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

theorem ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereRot {n : ℕ} (u : Fin n → Circle) :
    MeasurePreserving (sphereRot u) (sphereProb n) (sphereProb n) := by sorry
