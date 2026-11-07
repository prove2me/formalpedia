-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusNormalBasis_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusNormalBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:00.04992+00:00
-- url     : https://prove2.me/theorems/38f4a42e-32f0-4ba4-b81d-dfa90fb65d42
-- title:
--   Cartwright Steger: frobenius Normal Basis apply
-- statement:
--   The Cartwright Steger construction uses the frobenius Normal Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L307-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L307-L314

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusNormalBasis_apply (P : BasePrime) (r : Rank)
    (i : Fin r.matrixRank) :
    frobeniusNormalBasis P r i =
      (constantFrobenius P r ^ i.val)
        (IsGalois.normalBasis (BaseField P) (ConstantExtension P r) 1) := by sorry
