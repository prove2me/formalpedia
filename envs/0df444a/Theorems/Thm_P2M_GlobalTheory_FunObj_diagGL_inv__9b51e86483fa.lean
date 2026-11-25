-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FunObj_diagGL_inv__9b51e86483fa
-- name    : P2M_GlobalTheory_FunObj_diagGL_inv__9b51e86483fa
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:14.227721+00:00
-- url     : https://prove2.me/theorems/89ac7108-43db-44e5-83ce-52bc34405847
-- title:
--   P2 M Global Theory Fun Obj diag GL inv  9b51e86483fa: P2 M Global Theory Fun Obj diag GL inv  9b51e86483fa
-- statement:
--   The P2 M Global Theory Fun Obj diag GL inv  9b51e86483fa construction uses the P2 M Global Theory Fun Obj diag GL inv  9b51e86483fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L72-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem P2M_GlobalTheory_FunObj_diagGL_inv__9b51e86483fa (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ := by sorry

alias «GlobalTheory».«FunObj».«diagGL_inv'» := P2M_GlobalTheory_FunObj_diagGL_inv__9b51e86483fa
