-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
-- name    : QEC.Coding.KT19ReedSolomon.evaluation_mem_reedSolomonCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:10:24.806425+00:00
-- url     : https://prove2.me/theorems/d43e00de-7494-48c2-a22c-723fcf441770
-- title:
--   KT19 Reed Solomon: evaluation mem reed Solomon Code
-- statement:
--   Every bounded polynomial evaluation is a codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L125-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L125-L128

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators

theorem QEC.Coding.KT19ReedSolomon.evaluation_mem_reedSolomonCode (p l : Nat) [Fact p.Prime]
    (polynomial : Polynomial.degreeLT (ZMod p) l) :
    evaluationLinearMap p l polynomial ∈ (reedSolomonCode p l).carrier := by sorry
