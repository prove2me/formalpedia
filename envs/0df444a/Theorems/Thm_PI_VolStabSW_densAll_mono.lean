-- Prove2me | Theorems.Thm_PI_VolStabSW_densAll_mono
-- name    : PI.VolStabSW.densAll_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.729071+00:00
-- url     : https://prove2.me/theorems/c7ac0d02-b649-4e82-8bcd-8c6b6d1ecef7
-- title:
--   Vol Stab SW: dens All mono
-- statement:
--   The Vol Stab SW construction uses the dens All mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfSt.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfSt.lean#L80-L83

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

theorem PI.VolStabSW.densAll_mono {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X} {U U' : Set V}
    (h : DensAll μ f ι ν U') (hU : U ⊆ U') : DensAll μ f ι ν U := by sorry
