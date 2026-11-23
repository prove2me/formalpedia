-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DPEval2___add_038c2ae041a5
-- name    : P2M_GlobalTheory_DPEval2___add_038c2ae041a5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:42.972365+00:00
-- url     : https://prove2.me/theorems/56b64f64-dde0-40b8-95f5-4667e3d11e43
-- title:
--   P2 M Global Theory DPEval2   add 038c2ae041a5: P2 M Global Theory DPEval2   add 038c2ae041a5
-- statement:
--   The P2 M Global Theory DPEval2   add 038c2ae041a5 construction uses the P2 M Global Theory DPEval2   add 038c2ae041a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L82-L84

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

theorem P2M_GlobalTheory_DPEval2___add_038c2ae041a5 {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by sorry

alias «GlobalTheory».«DPEval2».«φ_add» := P2M_GlobalTheory_DPEval2___add_038c2ae041a5
