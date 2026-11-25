-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:29.014679+00:00
-- url     : https://prove2.me/theorems/f856aa2a-7b94-5507-bf88-16edb721ff61
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded coeff shifted a179fd9cccd0: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded coeff shifted a179fd9cccd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded coeff shifted a179fd9cccd0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded coeff shifted a179fd9cccd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L139-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
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
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0 (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) {y : (Polynomial Ω)}
    (hy : y ∈ shifted w d t u) (k : ℕ) : ∃ z ∈ gradedSpan w d t k, y.coeff (k + 1) = w u * z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«coeff_shifted» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0
