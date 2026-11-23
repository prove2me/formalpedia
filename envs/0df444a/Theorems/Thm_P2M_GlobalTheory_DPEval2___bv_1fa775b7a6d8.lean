-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8
-- name    : P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:43.453072+00:00
-- url     : https://prove2.me/theorems/ad7738db-1b17-498c-8462-730afa65f772
-- title:
--   P2 M Global Theory DPEval2   bv 1fa775b7a6d8: P2 M Global Theory DPEval2   bv 1fa775b7a6d8
-- statement:
--   The P2 M Global Theory DPEval2   bv 1fa775b7a6d8 construction uses the P2 M Global Theory DPEval2   bv 1fa775b7a6d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L79-L80

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

theorem P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8 (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by sorry

alias «GlobalTheory».«DPEval2».«φ_bv» := P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8
