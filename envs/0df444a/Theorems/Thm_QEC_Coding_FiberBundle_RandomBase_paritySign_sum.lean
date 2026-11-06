-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_paritySign_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.paritySign_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:01.936613+00:00
-- url     : https://prove2.me/theorems/70c883af-debc-441b-bc4a-dc22f39f16f1
-- title:
--   Random Base: parity Sign sum
-- statement:
--   The character of a parity sum factors into the product of bit characters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L304-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L304-L312

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

theorem QEC.Coding.FiberBundle.RandomBase.paritySign_sum
    {r : Nat} (A : Finset (Fin (3 * r))) (column : ColumnSample r) :
    paritySign (∑ a ∈ A, cond (column a) (1 : ZMod 2) 0) =
      ∏ a ∈ A, signedBit (column a) := by sorry
