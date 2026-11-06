-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_large_le
-- name    : QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_large_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:49.534188+00:00
-- url     : https://prove2.me/theorems/03215df9-ecbe-4fb1-b2b2-4ba156b451cc
-- title:
--   Random Base: parity Probability Base large le
-- statement:
--   For `1 ≤ p w`, the fixed-subset parity-zero base is at most `4/7`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L558-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L558-L571

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

theorem QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_large_le
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 1 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (4 : Real) / 7 := by sorry
