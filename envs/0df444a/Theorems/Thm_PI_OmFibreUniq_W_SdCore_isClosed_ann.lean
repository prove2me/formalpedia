-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_isClosed_ann
-- name    : PI.OmFibreUniq.W.SdCore.isClosed_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:30.880872+00:00
-- url     : https://prove2.me/theorems/f044dcdd-ddd6-4192-b937-e4260776a303
-- title:
--   Sd Core: is Closed ann
-- statement:
--   The Sd Core construction uses the is Closed ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L72-L77

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
include hχc

theorem PI.OmFibreUniq.W.SdCore.isClosed_ann : IsClosed (ann χ (M : Set V)) := by sorry
