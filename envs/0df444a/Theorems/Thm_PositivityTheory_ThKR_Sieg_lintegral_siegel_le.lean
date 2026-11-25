-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Sieg_lintegral_siegel_le
-- name    : PositivityTheory.ThKR.Sieg.lintegral_siegel_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:09.401385+00:00
-- url     : https://prove2.me/theorems/54f1fb29-838b-5e0b-82b1-d254581b8ebd
-- title:
--   Sieg: lintegral siegel le
-- statement:
--   The Sieg construction uses the lintegral siegel le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L216-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean#L216-L304

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}

theorem PositivityTheory.ThKR.Sieg.lintegral_siegel_le (μ : Measure G) [μ.IsHaarMeasure] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) [LocallyCompactSpace P]
    (τ : P → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → P) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, (haar : Measure P).map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • haar) {Ω : Set G}
    (hΩ : IsCompact Ω) (hΩτ : ∀ p ∈ Ω, ∃ h : p ∈ P, τ ⟨p, h⟩ = 0) (hc : ∀ m : P, m.1 ∈ K → ∀ t, a t * m = m * a t) :
    ∃ C : ℝ≥0, ∀ (D : Set (Fin r → ℝ)) (S : Set G), MeasurableSet D → MeasurableSet S →
      (∀ g ∈ S, ∃ p ∈ Ω, ∃ t ∈ D, ∃ k ∈ K, g = p * a t * k) →
      ∀ (f : G → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
        (∀ p ∈ Ω, ∀ t ∈ D, ∀ k ∈ K, f (p * a t * k) ≤ h t) →
        ∫⁻ g in S, f g ∂μ ≤ C * ∫⁻ t in D, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by sorry
