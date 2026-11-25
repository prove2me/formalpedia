-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:26.557751+00:00
-- url     : https://prove2.me/theorems/d7965673-1fa9-49ec-8e8d-3698554e3163
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists chain cffe35f4d0ae: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists chain cffe35f4d0ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists chain cffe35f4d0ae construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists chain cffe35f4d0ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L237-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L237-L268

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
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae [Module.Finite (MRing ι F) M] (hM : IsMultigrading ι M piece) :
    ∀ N₀ : Submodule (MRing ι F) M, IsGradedSub piece N₀ →
      ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
        (q : Fin n → Ideal (MRing ι F)),
        N 0 = N₀ ∧ N (Fin.last n) = ⊤ ∧
        ∀ j : Fin n, x j ∈ piece (c j) ∧
          N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
          (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
          ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«exists_chain» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae
