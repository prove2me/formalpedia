-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnParityZero_measureReal
-- name    : QEC.Coding.FiberBundle.RandomBase.columnParityZero_measureReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:38.626064+00:00
-- url     : https://prove2.me/theorems/f90afc72-d76c-4cb8-8d9c-881925bef917
-- title:
--   Random Base: column Parity Zero measure Real
-- statement:
--   Exact probability that a selected row subset has even parity in one column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L384-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L384-L408

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u

theorem QEC.Coding.FiberBundle.RandomBase.columnParityZero_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    (columnDistribution r Delta hDelta).toMeasure.real
        {column | ColumnParityZero A column} =
      (1 +
        (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2 := by sorry
