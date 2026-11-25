-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:46.931056+00:00
-- url     : https://prove2.me/theorems/e9f927cb-bd4c-40b1-bb70-419a2843deab
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded monomial mem 013043894e40: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded monomial mem 013043894e40
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded monomial mem 013043894e40 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded monomial mem 013043894e40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L123-L137

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40 (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) {n : ℕ} {x : Ω}
    (hx : x ∈ gradedSpan w d t n) : C x * X ^ n ∈ gradedModule q d t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«monomial_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40
