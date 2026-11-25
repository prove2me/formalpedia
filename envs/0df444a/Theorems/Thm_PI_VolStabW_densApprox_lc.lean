-- Prove2me | Theorems.Thm_PI_VolStabW_densApprox_lc
-- name    : PI.VolStabW.densApprox_lc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:45.448151+00:00
-- url     : https://prove2.me/theorems/731f929b-9bf5-4ed0-95ed-c79ddae37212
-- title:
--   Vol Stab W: dens Approx lc
-- statement:
--   The Vol Stab W construction uses the dens Approx lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVGen.lean#L170-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVGen.lean#L170-L347

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

theorem PI.VolStabW.densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by sorry
