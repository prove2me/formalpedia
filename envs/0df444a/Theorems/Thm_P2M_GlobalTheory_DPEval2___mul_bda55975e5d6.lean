-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___mul_bda55975e5d6
-- name    : P2M_GlobalTheory_DPEval2___mul_bda55975e5d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:12.701789+00:00
-- url     : https://prove2.me/theorems/e6023a68-3142-4a55-84c5-0ca3eabc16ea
-- title:
--   P2 M Global Theory DPEval2   mul bda55975e5d6: P2 M Global Theory DPEval2   mul bda55975e5d6
-- statement:
--   The P2 M Global Theory DPEval2   mul bda55975e5d6 construction uses the P2 M Global Theory DPEval2   mul bda55975e5d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L95-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L95-L116

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

theorem P2M_GlobalTheory_DPEval2___mul_bda55975e5d6 (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by sorry

alias «GlobalTheory».«DPEval2».«φ_mul» := P2M_GlobalTheory_DPEval2___mul_bda55975e5d6
