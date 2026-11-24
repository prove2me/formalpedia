-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:42.32224+00:00
-- url     : https://prove2.me/theorems/500ef0c3-f8f3-4be5-bc18-193b04447632
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul mem succ 43982fb32ce9: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul mem succ 43982fb32ce9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul mem succ 43982fb32ce9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded mul mem succ 43982fb32ce9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L17-L32

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9 (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) :
    x * w j ∈ gradedSpan w d t (k + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«mul_mem_succ» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9
