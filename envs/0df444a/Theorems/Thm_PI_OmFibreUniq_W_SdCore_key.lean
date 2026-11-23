-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_key
-- name    : PI.OmFibreUniq.W.SdCore.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:52.909018+00:00
-- url     : https://prove2.me/theorems/83845012-6630-48b0-8de2-37fc375b1c14
-- title:
--   Sd Core: key
-- statement:
--   The Sd Core construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L81-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L81-L128

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
variable (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
  (hn : ∀ x y, ‖χ x y‖ = 1)
  (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V) (hMc : IsCompact (M : Set V))
  (hMo : IsOpen (M : Set V))
include hχc hχ hsym hn hMc hMo

theorem PI.OmFibreUniq.W.SdCore.key (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) (z : V) :
    ∫ y in (M : Set V), (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ =
      (μ.real (M : Set V) : ℂ) * ∫ u in ann χ M, Φ (u - z) ∂μ := by sorry
