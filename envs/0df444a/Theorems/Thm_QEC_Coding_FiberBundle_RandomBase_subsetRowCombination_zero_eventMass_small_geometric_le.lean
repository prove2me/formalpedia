-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass_small_geometric_le
-- name    : QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass_small_geometric_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:30:06.215203+00:00
-- url     : https://prove2.me/theorems/caf10c05-06e2-4070-a82c-aebadd0d0b09
-- title:
--   Random Base: subset Row Combination zero event Mass small geometric le
-- statement:
--   After substituting `p = Delta / (4r)`, the small-weight estimate is a
--   geometric weight in the row-subset cardinality.  Keeping this dependence is
--   essential: replacing it by a uniform estimate would lose against the
--   `2^(3r)` possible row subsets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L616-L642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L616-L642

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

theorem QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass_small_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) ≤
      (ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ A.card := by sorry
