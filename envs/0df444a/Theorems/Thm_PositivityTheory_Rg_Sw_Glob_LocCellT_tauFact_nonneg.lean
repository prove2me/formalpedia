-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_LocCellT_tauFact_nonneg
-- name    : PositivityTheory.Rg.Sw.Glob.LocCellT.tauFact_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:40.780362+00:00
-- url     : https://prove2.me/theorems/d8207e13-d61c-44cf-a940-513960cc776d
-- title:
--   Loc Cell T: tau Fact nonneg
-- statement:
--   The Loc Cell T construction uses the tau Fact nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/LocCellT.lean#L13-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/LocCellT.lean#L13-L86

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_LocCellT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.LocCellT
variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [IsTopologicalAddGroup X]

theorem PositivityTheory.Rg.Sw.Glob.LocCellT.tauFact_nonneg (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (g : X → ℝ≥0) (hgm : Measurable g)
    (hg : ∀ x u, g (x + s u) = g x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ < ∞) :
    ∃ c : ℝ≥0, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a →
      ∫ z, a (π z) * (g z : ℂ) ∂μ = (c : ℂ) * ∫ u, a u := by sorry
