-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_charpoly_four
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:36.451192+00:00
-- url     : https://prove2.me/theorems/7d5e7272-8d75-48fd-a24d-fa8cb1f5d90f
-- title:
--   Cartwright Steger: frobenius GL charpoly four
-- statement:
--   The Cartwright Steger construction uses the frobenius GL charpoly four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L436-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L436-L453

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
set_option maxHeartbeats 800000

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_four (P : BasePrime) :
    (frobeniusGL P .four : Matrix (Fin Rank.four.matrixRank)
      (Fin Rank.four.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.four.matrixRank -
        (1 : Polynomial (BaseField P)) := by sorry
