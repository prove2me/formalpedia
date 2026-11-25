-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:43.454505+00:00
-- url     : https://prove2.me/theorems/4c7d7f48-0077-549a-aacb-1c4df872aac6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman filt Piece sup 19ebee9ad0cc: P2 M Ground Theory Heights  Heights Kleiman filt Piece sup 19ebee9ad0cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman filt Piece sup 19ebee9ad0cc construction uses the P2 M Ground Theory Heights  Heights Kleiman filt Piece sup 19ebee9ad0cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L395-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L395-L434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
variable {M₁ M₂}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} (hA : IsProjStable M₁ M₂ A) {e : ℤ}
    (g : M₁.piece e) (c : ℤ) :
    filtPiece M₁ M₂ (A ⊔ Submodule.span (Poly S N) {quotIota M₁ M₂ e g}) c =
      filtPiece M₁ M₂ A c ⊔ Submodule.span S
        {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • (g : E)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«filtPiece_sup» := P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_sup_19ebee9ad0cc
