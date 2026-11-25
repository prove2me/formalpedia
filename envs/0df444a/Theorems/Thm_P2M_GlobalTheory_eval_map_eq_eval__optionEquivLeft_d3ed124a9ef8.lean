-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eval_map_eq_eval__optionEquivLeft_d3ed124a9ef8
-- name    : P2M_GlobalTheory_eval_map_eq_eval__optionEquivLeft_d3ed124a9ef8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:04.031712+00:00
-- url     : https://prove2.me/theorems/58a9cd16-82a4-4e90-8143-aff04b1773a8
-- title:
--   P2 M Global Theory eval map eq eval  option Equiv Left d3ed124a9ef8: P2 M Global Theory eval map eq eval  option Equiv Left d3ed124a9ef8
-- statement:
--   The P2 M Global Theory eval map eq eval  option Equiv Left d3ed124a9ef8 construction uses the P2 M Global Theory eval map eq eval  option Equiv Left d3ed124a9ef8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L21-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
open MvPolynomial

theorem P2M_GlobalTheory_eval_map_eq_eval__optionEquivLeft_d3ed124a9ef8 (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (Q : Option (Fin n) → k) (p : MvPolynomial (Option (Fin n)) A) :
    eval Q (map ψ p) = Polynomial.eval₂ (eval₂Hom ψ (Q ∘ some)) (Q none) (optionEquivLeft A (Fin n) p) := by sorry

alias «GlobalTheory».«eval_map_eq_eval₂_optionEquivLeft» := P2M_GlobalTheory_eval_map_eq_eval__optionEquivLeft_d3ed124a9ef8
