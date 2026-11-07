-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_frobeniusNormalBasis
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_frobeniusNormalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:45.774193+00:00
-- url     : https://prove2.me/theorems/95fd7a2e-d1c5-462d-8816-9a867da35e94
-- title:
--   Cartwright Steger: constant Frobenius frobenius Normal Basis
-- statement:
--   The Cartwright Steger construction uses the constant Frobenius frobenius Normal Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L316-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L316-L345

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_frobeniusNormalBasis
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    constantFrobenius P r (frobeniusNormalBasis P r i) =
      frobeniusNormalBasis P r (finRotate r.matrixRank i) := by sorry
