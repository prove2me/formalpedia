-- Prove2me | Theorems.Thm_PI_VolStabSW_Glue_fibG_integral
-- name    : PI.VolStabSW.Glue.fibG_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:03.772582+00:00
-- url     : https://prove2.me/theorems/7a78ff9d-90b9-4ee9-9312-3d67eb5d2f82
-- title:
--   Glue: fib G integral
-- statement:
--   The Glue construction uses the fib G integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibGlue.lean#L244-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibGlue.lean#L244-L258

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.Glue
open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]

theorem PI.VolStabSW.Glue.fibG_integral (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) (φ : V → ℝ)
    (h : IsCcOn U φ) :
    Integrable φ (fibG hD hU b) ∧ ∫ v, φ v ∂(fibG hD hU b) = G hD φ b := by sorry
