-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:33.525905+00:00
-- url     : https://prove2.me/theorems/7d4ef31a-4947-5991-adb3-238c14ee1a15
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded smul coeff mem 5255ac3f8e81: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded smul coeff mem 5255ac3f8e81
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded smul coeff mem 5255ac3f8e81 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded smul coeff mem 5255ac3f8e81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L82-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L82-L104

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81 (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w)
    (c : MvPolynomial (Fin q) ℤ) {p : (Polynomial Ω)} (hp : ∀ n, p.coeff n ∈ gradedSpan w d t n) :
    ∀ n, (c • p).coeff n ∈ gradedSpan w d t n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«smul_coeff_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81
