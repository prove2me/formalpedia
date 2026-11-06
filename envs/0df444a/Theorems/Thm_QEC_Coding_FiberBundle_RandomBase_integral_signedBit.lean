-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_integral_signedBit
-- name    : QEC.Coding.FiberBundle.RandomBase.integral_signedBit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:29:01.904109+00:00
-- url     : https://prove2.me/theorems/b04eea45-8786-4afc-ac19-cfc8ff861c19
-- title:
--   Random Base: integral signed Bit
-- statement:
--   The expectation of one signed Bernoulli incidence is `1 - 2p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L315-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L315-L334

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

theorem QEC.Coding.FiberBundle.RandomBase.integral_signedBit
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ∫ column, signedBit (column a) ∂
        (columnDistribution r Delta hDelta).toMeasure =
      1 - 2 * (incidenceProbability (4 * r) Delta).toReal := by sorry
