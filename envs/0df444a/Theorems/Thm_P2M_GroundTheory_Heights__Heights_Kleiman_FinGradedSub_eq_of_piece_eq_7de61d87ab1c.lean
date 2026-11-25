-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:00.911844+00:00
-- url     : https://prove2.me/theorems/79958787-b03f-4406-9437-e5d41e40ca64
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq of piece eq 7de61d87ab1c: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq of piece eq 7de61d87ab1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq of piece eq 7de61d87ab1c construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq of piece eq 7de61d87ab1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L301-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L301-L306

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c {A B : FinGradedSub (S := S) (x := x) E} (h : A.piece = B.piece) :
    A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«eq_of_piece_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c
