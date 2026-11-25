-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_differentiable_exp_mul_of_annihilated__e8f45fb8d7db
-- name    : P2M_GlobalTheory_T_differentiable_exp_mul_of_annihilated__e8f45fb8d7db
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:04.100037+00:00
-- url     : https://prove2.me/theorems/3f0cd3b3-aabb-4f2a-ab43-c4c8303be97f
-- title:
--   P2 M Global Theory T differentiable exp mul of annihilated  e8f45fb8d7db: P2 M Global Theory T differentiable exp mul of annihilated  e8f45fb8d7db
-- statement:
--   The P2 M Global Theory T differentiable exp mul of annihilated  e8f45fb8d7db construction uses the P2 M Global Theory T differentiable exp mul of annihilated  e8f45fb8d7db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DifferentiableExpMulOfAnnihilatedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DifferentiableExpMulOfAnnihilatedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DifferentiableExpMulOfAnnihilated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DifferentiableExpMulOfAnnihilatedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_differentiable_exp_mul_of_annihilated__e8f45fb8d7db : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by sorry

alias «GlobalTheory».«T».«differentiable_exp_mul_of_annihilated'» := P2M_GlobalTheory_T_differentiable_exp_mul_of_annihilated__e8f45fb8d7db
