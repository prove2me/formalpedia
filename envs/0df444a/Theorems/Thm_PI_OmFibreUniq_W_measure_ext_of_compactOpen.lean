-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_measure_ext_of_compactOpen
-- name    : PI.OmFibreUniq.W.measure_ext_of_compactOpen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:41.653258+00:00
-- url     : https://prove2.me/theorems/e2a13015-5777-52e3-9697-b08d0e513cb8
-- title:
--   W: measure ext of compact Open
-- statement:
--   The W construction uses the measure ext of compact Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L45-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L45-L82

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
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V]
variable [SecondCountableTopology V]
variable [MeasurableSpace V] [BorelSpace V]

theorem PI.OmFibreUniq.W.measure_ext_of_compactOpen {U : Set V} (hU : IsOpen U) (m m' : Measure V)
    (h0 : m Uᶜ = 0) (h0' : m' Uᶜ = 0)
    (hK : ∀ K, IsCompact K → IsOpen K → K ⊆ U → m K < ∞ ∧ m K = m' K) : m = m' := by sorry
