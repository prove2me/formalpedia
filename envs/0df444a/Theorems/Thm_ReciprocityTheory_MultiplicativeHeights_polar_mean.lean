-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_polar_mean
-- name    : ReciprocityTheory.MultiplicativeHeights.polar_mean
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:42.986986+00:00
-- url     : https://prove2.me/theorems/ee246e87-62d4-5993-8eab-f644fc0c9c52
-- title:
--   Multiplicative Heights: polar mean
-- statement:
--   The Multiplicative Heights construction uses the polar mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreD.lean#L30-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreD.lean#L30-L131

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
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
open MeasureTheory Metric Set Real

theorem ReciprocityTheory.MultiplicativeHeights.polar_mean {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    Integrable (fun z : UnitSphereC n ↦ log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        gaussLogC ‖c‖ / gaussOneC - radK (2 * n - 1) / radJ (2 * n - 1) := by sorry
