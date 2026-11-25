-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_chi_zero_left
-- name    : PI.OmFibreUniq.W.SdCore.chi_zero_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:43.397801+00:00
-- url     : https://prove2.me/theorems/be9f474d-ee1d-5e4f-8ee0-ae3a1082ee43
-- title:
--   Sd Core: chi zero left
-- statement:
--   The Sd Core construction uses the chi zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L15-L27

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

theorem PI.OmFibreUniq.W.SdCore.chi_zero_left (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hn : ∀ x y, ‖χ x y‖ = 1) (y : V) : χ 0 y = 1 := by sorry
