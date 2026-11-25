-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_L2_skew
-- name    : PositivityTheory.ThKF.L2.skew
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:44.611386+00:00
-- url     : https://prove2.me/theorems/5960e54c-69f8-4d6e-a409-472df171aaaa
-- title:
--   L2: skew
-- statement:
--   The L2 construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L106-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean#L106-L125

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

theorem PositivityTheory.ThKF.L2.skew [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {f f₁ g g₁ : G → ℂ} (cf : Continuous f) (cf₁ : Continuous f₁) (cg : Continuous g) (cg₁ : Continuous g₁)
    (hf : Inv Γ f) (hf₁ : Inv Γ f₁) (hg : Inv Γ g) (hg₁ : Inv Γ g₁)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (f₁2 : IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ)
    (g2 : IntegrableOn (fun x => ‖g x‖ ^ 2) 𝓕 μ) (g₁2 : IntegrableOn (fun x => ‖g₁ x‖ ^ 2) 𝓕 μ)
    (df : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0)
    (dg : ∀ x, HasDerivAt (fun t : ℝ => g (x * γ (Multiplicative.ofAdd t))) (g₁ x) 0) :
    ∫ x in 𝓕, conj (f₁ x) * g x ∂μ + ∫ x in 𝓕, conj (f x) * g₁ x ∂μ = 0 := by sorry
