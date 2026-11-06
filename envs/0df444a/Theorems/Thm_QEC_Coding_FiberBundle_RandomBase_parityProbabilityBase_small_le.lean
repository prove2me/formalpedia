-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_small_le
-- name    : QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_small_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:47.646207+00:00
-- url     : https://prove2.me/theorems/7c9bdea3-3697-4e90-a7cd-fb8c31a9b7a7
-- title:
--   Random Base: parity Probability Base small le
-- statement:
--   For `p w ≤ 1`, the fixed-subset parity-zero base has the HHO20 small-weight
--   bound `exp(-p w / 2)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L521-L543
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L521-L543

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

theorem QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_small_le
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hsmall : p * w ≤ 1) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 2) := by sorry
