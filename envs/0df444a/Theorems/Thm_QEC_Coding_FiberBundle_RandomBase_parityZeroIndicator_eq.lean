-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityZeroIndicator_eq
-- name    : QEC.Coding.FiberBundle.RandomBase.parityZeroIndicator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:17.312046+00:00
-- url     : https://prove2.me/theorems/27ddc8d6-d0f7-4f47-9516-e828336e663b
-- title:
--   Random Base: parity Zero Indicator eq
-- statement:
--   Fourier character identity for the even-parity indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L369-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L369-L381

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

theorem QEC.Coding.FiberBundle.RandomBase.parityZeroIndicator_eq
    {r : Nat} (A : Finset (Fin (3 * r))) (column : ColumnSample r) :
    parityZeroIndicator A column =
      (1 + ∏ a ∈ A, signedBit (column a)) / 2 := by sorry
