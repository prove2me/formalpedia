-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_exists_normalized
-- name    : PI.OmFibreUniq.W.SdCore.exists_normalized
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:06.989035+00:00
-- url     : https://prove2.me/theorems/07a86f0c-fbe5-4123-9871-77d4381300d0
-- title:
--   Sd Core: exists normalized
-- statement:
--   The Sd Core construction uses the exists normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L35-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L35-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem PI.OmFibreUniq.W.SdCore.exists_normalized (μ0 : Measure V) [μ0.IsAddHaarMeasure] (A B : ℕ → Set V)
    (hAc : ∀ k, IsCompact (A k)) (hBc : ∀ k, IsCompact (B k)) (hAo : IsOpen (A 0))
    (hBo : IsOpen (B 0)) (hA0 : (A 0).Nonempty) (hB0 : (B 0).Nonempty)
    (hconst : ∀ k, μ0 (A k) * μ0 (B k) = μ0 (A 0) * μ0 (B 0)) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ ∀ k, μ.real (A k) * μ.real (B k) = 1 := by sorry
