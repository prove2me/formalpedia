-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896
-- name    : P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:12.916845+00:00
-- url     : https://prove2.me/theorems/5e11a20d-8fa3-4b2f-8367-09e057fd2d85
-- title:
--   P2 M Global Theory Fun Obj diag GL mul  bb3860aff896: P2 M Global Theory Fun Obj diag GL mul  bb3860aff896
-- statement:
--   The P2 M Global Theory Fun Obj diag GL mul  bb3860aff896 construction uses the P2 M Global Theory Fun Obj diag GL mul  bb3860aff896 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L69-L70

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

theorem P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896 (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e := by sorry

alias «GlobalTheory».«FunObj».«diagGL_mul'» := P2M_GlobalTheory_FunObj_diagGL_mul__bb3860aff896
