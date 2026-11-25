-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:39.902302+00:00
-- url     : https://prove2.me/theorems/f64ec626-7303-4611-97ee-3ec26c84eb31
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul pow mem 8f4bb2b91237: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul pow mem 8f4bb2b91237
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul pow mem 8f4bb2b91237 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul pow mem 8f4bb2b91237 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L34-L41

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237 (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) (e : ℕ) :
    x * w j ^ e ∈ gradedSpan w d t (k + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«mul_pow_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237
