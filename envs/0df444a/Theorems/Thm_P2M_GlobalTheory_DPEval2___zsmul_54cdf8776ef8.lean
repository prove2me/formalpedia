-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8
-- name    : P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:23.269971+00:00
-- url     : https://prove2.me/theorems/8d0923f4-faaf-4bdd-930c-6d7804e20055
-- title:
--   P2 M Global Theory DPEval2   zsmul 54cdf8776ef8: P2 M Global Theory DPEval2   zsmul 54cdf8776ef8
-- statement:
--   The P2 M Global Theory DPEval2   zsmul 54cdf8776ef8 construction uses the P2 M Global Theory DPEval2   zsmul 54cdf8776ef8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L86-L87

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

theorem P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8 (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by sorry

alias «GlobalTheory».«DPEval2».«φ_zsmul» := P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8
