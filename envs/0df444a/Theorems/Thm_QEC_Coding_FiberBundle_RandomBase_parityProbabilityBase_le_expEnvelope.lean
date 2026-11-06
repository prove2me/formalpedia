-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_le_expEnvelope
-- name    : QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_le_expEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:11.076847+00:00
-- url     : https://prove2.me/theorems/c87ea72c-5e39-4be4-aee1-675340208c95
-- title:
--   Random Base: parity Probability Base le exp Envelope
-- statement:
--   Exponential envelope for the parity-zero base at a fixed subset weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L498-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L498-L515

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

theorem QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_le_expEnvelope
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      (1 + Real.exp (-2 * (p * w))) / 2 := by sorry
