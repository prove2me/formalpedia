-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdCore_selfDual_of_pairs
-- name    : PI.OmFibreUniq.W.SdCore.selfDual_of_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:56.507681+00:00
-- url     : https://prove2.me/theorems/74823557-7620-4e87-8b9d-7155ebc7850c
-- title:
--   Sd Core: self Dual of pairs
-- statement:
--   The Sd Core construction uses the self Dual of pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L132-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean#L132-L195

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

theorem PI.OmFibreUniq.W.SdCore.selfDual_of_pairs (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1)
    (M : ℕ → AddSubgroup V) (hMc : ∀ k, IsCompact (M k : Set V)) (hMo : ∀ k, IsOpen (M k : Set V))
    (hNc : ∀ k, IsCompact (ann χ (M k))) (hNo : ∀ k, IsOpen (ann χ (M k)))
    (hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k)
    (hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k) ⊆ U)
    (μ0 : Measure V) [μ0.IsAddHaarMeasure]
    (hconst : ∀ k, μ0 (M k) * μ0 (ann χ (M k)) = μ0 (M 0) * μ0 (ann χ (M 0))) :
    ∃ μ : Measure V, SelfDual μ χ := by sorry
