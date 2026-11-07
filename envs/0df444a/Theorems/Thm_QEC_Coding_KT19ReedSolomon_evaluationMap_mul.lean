-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluationMap_mul
-- name    : QEC.Coding.KT19ReedSolomon.evaluationMap_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:16.381438+00:00
-- url     : https://prove2.me/theorems/38822f06-f617-486a-8e09-dd9ebb340a28
-- title:
--   KT19 Reed Solomon: evaluation Map mul
-- statement:
--   The KT19 Reed Solomon construction uses the evaluation Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L59-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L59-L64

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

theorem QEC.Coding.KT19ReedSolomon.evaluationMap_mul (p : Nat)
    (left right : Polynomial (ZMod p)) :
    evaluationMap p (left * right) =
      coordinatewiseProduct (evaluationMap p left) (evaluationMap p right) := by sorry
