-- Prove2me | Theorems.Thm_PI_VolStabSW_densAll_of_local
-- name    : PI.VolStabSW.densAll_of_local
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:42:22.540473+00:00
-- url     : https://prove2.me/theorems/b7b5bb4d-2599-4674-bc58-9ac172cdccdd
-- title:
--   Vol Stab SW: dens All of local
-- statement:
--   The Vol Stab SW construction uses the dens All of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfSt.lean#L85-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfSt.lean#L85-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

theorem PI.VolStabSW.densAll_of_local [T2Space V] [LocallyCompactSpace V] [OpensMeasurableSpace V]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure V} [IsFiniteMeasureOnCompacts μ] {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] {f : V → Y} {ι : X → Y} {U : Set V}
    (h : ∀ x ∈ U, ∃ N, IsOpen N ∧ x ∈ N ∧ DensAll μ f ι ν N) : DensAll μ f ι ν U := by sorry
