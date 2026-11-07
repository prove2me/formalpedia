-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_charpoly_three
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:13.573115+00:00
-- url     : https://prove2.me/theorems/6224ce61-b3b0-4b1f-8477-f26906a725e9
-- title:
--   Cartwright Steger: frobenius GL charpoly three
-- statement:
--   The Cartwright Steger construction uses the frobenius GL charpoly three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L416-L433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L416-L433

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_three (P : BasePrime) :
    (frobeniusGL P .three : Matrix (Fin Rank.three.matrixRank)
      (Fin Rank.three.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.three.matrixRank -
        (1 : Polynomial (BaseField P)) := by sorry
