-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b
-- name    : P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:36.914622+00:00
-- url     : https://prove2.me/theorems/69431373-d5cf-438b-8c24-2baed079a031
-- title:
--   P2 M Global Theory DPEval2   of mem bf3d58ee089b: P2 M Global Theory DPEval2   of mem bf3d58ee089b
-- statement:
--   The P2 M Global Theory DPEval2   of mem bf3d58ee089b construction uses the P2 M Global Theory DPEval2   of mem bf3d58ee089b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L77-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L77-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
variable {B : Type} [CommRing B] (u v : ℕ → B)

theorem P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) : φ u v q = ψ u v ⟨q, h⟩ := by sorry

alias «GlobalTheory».«DPEval2».«φ_of_mem» := P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b
