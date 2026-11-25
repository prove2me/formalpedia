-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:57.94991+00:00
-- url     : https://prove2.me/theorems/15f54622-c0b8-4556-a27f-d1487d92d108
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms ordered 254d16ac3e24: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms ordered 254d16ac3e24 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms ordered 254d16ac3e24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L143-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L143-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24 {σ L : Type*} [AddCommMonoid L] [LinearOrder L]
    [IsOrderedCancelAddMonoid L] (w : σ → L) (q : Ideal (MvPolynomial σ F))
    (hq : ∀ r ∈ q, ∀ i, weightedHomogeneousComponent w i r ∈ q) (hne : q ≠ ⊤)
    (h : ∀ a b : MvPolynomial σ F, (∃ i, IsWeightedHomogeneous w a i) →
      (∃ j, IsWeightedHomogeneous w b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«isPrime_of_forms_ordered» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_ordered_254d16ac3e24
