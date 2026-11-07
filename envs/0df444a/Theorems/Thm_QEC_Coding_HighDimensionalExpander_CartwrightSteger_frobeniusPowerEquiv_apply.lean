-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:19.362891+00:00
-- url     : https://prove2.me/theorems/32bcc9a0-3909-46f9-903d-bef12a9f5da7
-- title:
--   Cartwright Steger: frobenius Power Equiv apply
-- statement:
--   The Cartwright Steger construction uses the frobenius Power Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L296-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L296-L299

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    frobeniusPowerEquiv P r i = constantFrobenius P r ^ i.val := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
