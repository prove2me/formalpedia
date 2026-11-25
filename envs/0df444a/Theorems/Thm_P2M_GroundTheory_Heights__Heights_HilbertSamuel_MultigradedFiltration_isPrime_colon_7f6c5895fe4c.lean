-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:10.880011+00:00
-- url     : https://prove2.me/theorems/a6fcf84e-a0ac-4291-86d2-dba0665ce28e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime colon 7f6c5895fe4c: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime colon 7f6c5895
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime colon 7f6c5895fe4c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration is Prime colon 7f6c5895fe4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L198-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L198-L222

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) (hxN : x ∉ N)
    (hmax : ∀ (c' : K → ℤ) (y : M), y ∈ piece c' → y ∉ N → ¬ N.colon {x} < N.colon {y}) :
    (N.colon {x}).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«isPrime_colon» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c
