-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LaurentFJ_coeff_eq_zero_of_mem_SSgt__e61e43d67a3b
-- name    : P2M_GlobalTheory_LaurentFJ_coeff_eq_zero_of_mem_SSgt__e61e43d67a3b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:25.542896+00:00
-- url     : https://prove2.me/theorems/373dc292-2f2e-5477-9853-54c3636377f1
-- title:
--   P2 M Global Theory Laurent FJ coeff eq zero of mem SSgt  e61e43d67a3b: P2 M Global Theory Laurent FJ coeff eq zero of mem SSgt  e61e43d67a3b
-- statement:
--   The P2 M Global Theory Laurent FJ coeff eq zero of mem SSgt  e61e43d67a3b construction uses the P2 M Global Theory Laurent FJ coeff eq zero of mem SSgt  e61e43d67a3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L209-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L209-L221

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem P2M_GlobalTheory_LaurentFJ_coeff_eq_zero_of_mem_SSgt__e61e43d67a3b (X : Data E r) {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt la c) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (hν₀ : ∑ τ, ν₀ τ ≤ c) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (hu₁ : u₁ ≠ 0) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j = 0 := by sorry

alias «GlobalTheory».«LaurentFJ».«coeff_eq_zero_of_mem_SSgt'» := P2M_GlobalTheory_LaurentFJ_coeff_eq_zero_of_mem_SSgt__e61e43d67a3b
