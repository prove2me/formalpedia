-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_rotS
-- name    : ReciprocityTheory.MultiplicativeHeights.measurePreserving_rotS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:33.743991+00:00
-- url     : https://prove2.me/theorems/5c5a21e3-ace6-49cf-a60b-4b947f0ea9ac
-- title:
--   Multiplicative Heights: measure Preserving rot S
-- statement:
--   The Multiplicative Heights construction uses the measure Preserving rot S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L95-L97

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

theorem ReciprocityTheory.MultiplicativeHeights.measurePreserving_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotS hu θ) (sphereProb n) (sphereProb n) := by sorry
