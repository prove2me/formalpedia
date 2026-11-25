-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9
-- name    : P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:11.046913+00:00
-- url     : https://prove2.me/theorems/78ce0a42-ab43-471e-b1c6-0d0719027b70
-- title:
--   P2 M Global Theory DPEval2   nsmul 635e58ae52b9: P2 M Global Theory DPEval2   nsmul 635e58ae52b9
-- statement:
--   The P2 M Global Theory DPEval2   nsmul 635e58ae52b9 construction uses the P2 M Global Theory DPEval2   nsmul 635e58ae52b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L89-L90

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

theorem P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9 (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by sorry

alias «GlobalTheory».«DPEval2».«φ_nsmul» := P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9
