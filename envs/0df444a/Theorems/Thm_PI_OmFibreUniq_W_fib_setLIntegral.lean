-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_fib_setLIntegral
-- name    : PI.OmFibreUniq.W.fib_setLIntegral
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:10.140967+00:00
-- url     : https://prove2.me/theorems/18043e63-ac6b-57a2-9f7b-fd288831d514
-- title:
--   W: fib set LIntegral
-- statement:
--   The W construction uses the fib set LIntegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L124-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L124-L156

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

theorem PI.OmFibreUniq.W.fib_setLIntegral (hA : ∀ S : Set X, MeasurableSet S → MeasurableSet (f ⁻¹' (ι '' S)))
    (hι : Function.Injective ι) {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν Set.univ fib)
    {K : Set V} (hKm : MeasurableSet K) (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ b in S, fib b K ∂ν = ∫⁻ x in U, (K ∩ f ⁻¹' (ι '' S)).indicator 1 x ∂μ := by sorry
