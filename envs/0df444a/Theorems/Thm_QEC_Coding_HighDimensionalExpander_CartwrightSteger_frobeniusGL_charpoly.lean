-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_charpoly
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:06.842358+00:00
-- url     : https://prove2.me/theorems/d70d7a04-1881-4717-b94a-3d83f76802c4
-- title:
--   Cartwright Steger: frobenius GL charpoly
-- statement:
--   Arithmetic Frobenius has the full-cycle characteristic polynomial in
--   the fixed construction basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L457-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L457-L463

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly (P : BasePrime) (r : Rank) :
    (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ r.matrixRank - 1 := by sorry
