-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1
-- name    : P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:51.343898+00:00
-- url     : https://prove2.me/theorems/8ae2bc23-fe31-40cf-b1df-e8e7eb1d51e7
-- title:
--   P2 M Global Theory is Scheme Theoretically Dominant   of germ eq zero over affine 6b5f7e9382c1: P2 M Global Theory is Scheme Theoretically Dominant   of germ eq zero over affine 6b5f7e9382c1
-- statement:
--   The P2 M Global Theory is Scheme Theoretically Dominant   of germ eq zero over affine 6b5f7e9382c1 construction uses the P2 M Global Theory is Scheme Theoretically Dominant   of germ eq zero over affine 6b5f7e9382c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchemeTheoreticallyDominantOfGermInjective.lean#L6-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchemeTheoreticallyDominantOfGermInjective.lean#L6-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1
    (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens)
    (h : ∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) :
    IsSchemeTheoreticallyDominant W.ι := by sorry

alias «GlobalTheory».«isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine» := P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1
