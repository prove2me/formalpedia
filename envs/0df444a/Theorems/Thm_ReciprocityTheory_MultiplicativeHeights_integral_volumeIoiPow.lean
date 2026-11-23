-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_volumeIoiPow
-- name    : ReciprocityTheory.MultiplicativeHeights.integral_volumeIoiPow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:08.838261+00:00
-- url     : https://prove2.me/theorems/af44382b-85b9-4840-a862-6c4ab4cbc32c
-- title:
--   Multiplicative Heights: integral volume Ioi Pow
-- statement:
--   The Multiplicative Heights construction uses the integral volume Ioi Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L10-L17

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

theorem ReciprocityTheory.MultiplicativeHeights.integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by sorry
