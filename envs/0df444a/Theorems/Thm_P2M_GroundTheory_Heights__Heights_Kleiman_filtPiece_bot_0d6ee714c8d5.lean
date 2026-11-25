-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:01.134867+00:00
-- url     : https://prove2.me/theorems/7fedc9bd-dcaf-4e67-b4f5-645429f56ca8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman filt Piece bot 0d6ee714c8d5: P2 M Ground Theory Heights  Heights Kleiman filt Piece bot 0d6ee714c8d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman filt Piece bot 0d6ee714c8d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman filt Piece bot 0d6ee714c8d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L333-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L333-L341

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5 (hle : ∀ c, M₂.piece c ≤ M₁.piece c) (c : ℤ) :
    filtPiece M₁ M₂ ⊥ c = M₂.piece c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«filtPiece_bot» := P2M_GroundTheory_Heights__Heights_Kleiman_filtPiece_bot_0d6ee714c8d5
