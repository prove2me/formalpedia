-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass_small_le
-- name    : QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass_small_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:29:53.233369+00:00
-- url     : https://prove2.me/theorems/7eb0e045-816e-4f9e-9690-7f5644aa98b1
-- title:
--   Random Base: subset Row Combination zero event Mass small le
-- statement:
--   Fixed-subset event-mass bound in the paper's small-weight regime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L574-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L574-L608

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

theorem QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass_small_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal
        (Real.exp
          (-((incidenceProbability (4 * r) Delta).toReal * A.card) / 2))) ^
        (4 * r) := by sorry
