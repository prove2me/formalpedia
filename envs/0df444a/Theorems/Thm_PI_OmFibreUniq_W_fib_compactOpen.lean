-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_fib_compactOpen
-- name    : PI.OmFibreUniq.W.fib_compactOpen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:58.859469+00:00
-- url     : https://prove2.me/theorems/53f859c9-eca5-51e0-a8b9-7caec7824c05
-- title:
--   W: fib compact Open
-- statement:
--   The W construction uses the fib compact Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L93-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L93-L119

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

theorem PI.OmFibreUniq.W.fib_compactOpen {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
    {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν Set.univ fib) {K : Set V}
    (hKc : IsCompact K) (hKo : IsOpen K) (hKU : K ⊆ U) :
    (∀ b, fib b K < ∞) ∧ Continuous (fun b => (fib b K).toReal) := by sorry
