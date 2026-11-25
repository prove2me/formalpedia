-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:04.454803+00:00
-- url     : https://prove2.me/theorems/7844a9e4-5d97-43b1-ad5c-98155ccb8c1f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coe mem filt Piece dc3e1604a1b8: P2 M Ground Theory Heights  Heights Kleiman coe mem filt Piece dc3e1604a1b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coe mem filt Piece dc3e1604a1b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman coe mem filt Piece dc3e1604a1b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L323-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L323-L325

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8 {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} {c : ℤ} (z : M₁.piece c) :
    (z : E) ∈ filtPiece M₁ M₂ A c ↔ quotIota M₁ M₂ c z ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coe_mem_filtPiece» := P2M_GroundTheory_Heights__Heights_Kleiman_coe_mem_filtPiece_dc3e1604a1b8
