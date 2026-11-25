-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_zero_mem_ann
-- name    : PI.OmFibreUniq.W.SdCore.zero_mem_ann
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:37.34043+00:00
-- url     : https://prove2.me/theorems/7032d123-0ccb-5693-86d5-8cd5c1b8f7fd
-- title:
--   Sd Core: zero mem ann
-- statement:
--   The Sd Core construction uses the zero mem ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L29-L33

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

theorem PI.OmFibreUniq.W.SdCore.zero_mem_ann (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hsym : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1) (L : Set V) : (0 : V) ∈ ann χ L := by sorry
