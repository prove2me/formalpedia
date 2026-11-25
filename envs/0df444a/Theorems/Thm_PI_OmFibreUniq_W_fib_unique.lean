-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_fib_unique
-- name    : PI.OmFibreUniq.W.fib_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:19.849803+00:00
-- url     : https://prove2.me/theorems/28d30b9b-4d44-4b47-9db4-5144f0337df5
-- title:
--   W: fib unique
-- statement:
--   The W construction uses the fib unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L158-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L158-L187

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
variable {V X Y : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]
variable (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
  (f : V → Y) (ι : X → Y) (U : Set V)

theorem PI.OmFibreUniq.W.fib_unique (hA : ∀ S : Set X, MeasurableSet S → MeasurableSet (f ⁻¹' (ι '' S)))
    (hι : Function.Injective ι) (hU : IsOpen U) (fib fib' : X → Measure V)
    (h : IsFibreFamily μ f ι U ν Set.univ fib) (h' : IsFibreFamily μ f ι U ν Set.univ fib') :
    fib = fib' := by sorry
