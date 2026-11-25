-- Prove2me | Theorems.Thm_PI_VolStabSW_densLC_of_cosB
-- name    : PI.VolStabSW.densLC_of_cosB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:32.222062+00:00
-- url     : https://prove2.me/theorems/4b1ee1df-d3b4-4f74-8ef4-1bc7605cf9a2
-- title:
--   Vol Stab SW: dens LC of cos B
-- statement:
--   The Vol Stab SW construction uses the dens LC of cos B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensVCos.lean#L96-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensVCos.lean#L96-L195

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
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
open MeasureTheory Topology Set Filter
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem PI.VolStabSW.densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν := by sorry
