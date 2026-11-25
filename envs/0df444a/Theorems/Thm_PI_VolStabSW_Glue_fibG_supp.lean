-- Prove2me | Theorems.Thm_PI_VolStabSW_Glue_fibG_supp
-- name    : PI.VolStabSW.Glue.fibG_supp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:47.678788+00:00
-- url     : https://prove2.me/theorems/fd902f69-fdfe-54c7-8c8f-367a04d91bad
-- title:
--   Glue: fib G supp
-- statement:
--   The Glue construction uses the fib G supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibGlue.lean#L276-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibGlue.lean#L276-L324

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

theorem PI.VolStabSW.Glue.fibG_supp (hD : DensAll μ f ι ν U) (hU : IsOpen U) (hf : Continuous f)
    (hι : Continuous ι) (b : X) : fibG hD hU b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := by sorry
