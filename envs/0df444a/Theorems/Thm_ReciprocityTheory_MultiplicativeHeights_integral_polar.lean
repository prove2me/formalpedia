-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_polar
-- name    : ReciprocityTheory.MultiplicativeHeights.integral_polar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:37.106976+00:00
-- url     : https://prove2.me/theorems/2e82b48f-09be-5597-9614-9b95cda4ee71
-- title:
--   Multiplicative Heights: integral polar
-- statement:
--   The Multiplicative Heights construction uses the integral polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L40-L54

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
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

theorem ReciprocityTheory.MultiplicativeHeights.integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by sorry
