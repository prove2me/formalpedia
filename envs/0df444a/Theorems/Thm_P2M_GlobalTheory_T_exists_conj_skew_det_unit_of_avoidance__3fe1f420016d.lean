-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_conj_skew_det_unit_of_avoidance__3fe1f420016d
-- name    : P2M_GlobalTheory_T_exists_conj_skew_det_unit_of_avoidance__3fe1f420016d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:16.257887+00:00
-- url     : https://prove2.me/theorems/c8edecb7-928f-4b1a-8539-45f2536e0547
-- title:
--   P2 M Global Theory T exists conj skew det unit of avoidance  3fe1f420016d: P2 M Global Theory T exists conj skew det unit of avoidance  3fe1f420016d
-- statement:
--   The P2 M Global Theory T exists conj skew det unit of avoidance  3fe1f420016d construction uses the P2 M Global Theory T exists conj skew det unit of avoidance  3fe1f420016d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjSkewDetUnitOfAvoidanceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjSkewDetUnitOfAvoidanceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConjSkewDetUnitOfAvoidance
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConjSkewDetUnitOfAvoidanceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_conj_skew_det_unit_of_avoidance__3fe1f420016d : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by sorry

alias «GlobalTheory».«T».«exists_conj_skew_det_unit_of_avoidance'» := P2M_GlobalTheory_T_exists_conj_skew_det_unit_of_avoidance__3fe1f420016d
