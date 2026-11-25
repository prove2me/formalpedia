-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:10.566476+00:00
-- url     : https://prove2.me/theorems/98d1837a-9221-466d-bb6a-fd39d48d8200
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms 48f55a7aabc8: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms 48
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms 48f55a7aabc8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime of forms 48f55a7aabc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L160-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L160-L192

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8 (q : Ideal (MRing ι F)) (hq : IsMultiHomogIdeal q) (hne : q ≠ ⊤)
    (h : ∀ a b : MRing ι F, (∃ i, IsWeightedHomogeneous (blockWeight ι) a i) →
      (∃ j, IsWeightedHomogeneous (blockWeight ι) b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«isPrime_of_forms» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8
