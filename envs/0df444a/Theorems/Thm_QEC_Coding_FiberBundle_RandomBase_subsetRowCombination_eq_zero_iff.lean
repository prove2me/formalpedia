-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_eq_zero_iff
-- name    : QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:58.70996+00:00
-- url     : https://prove2.me/theorems/e95312d0-79f2-489e-8d1a-cd66cfd066dc
-- title:
--   Random Base: subset Row Combination eq zero iff
-- statement:
--   Vanishing of a selected row sum is the all-column parity-zero event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L432-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L432-L451

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

theorem QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_eq_zero_iff
    {r : Nat} (sample : Sample r)
    (A : Finset (Fin (3 * r))) :
    subsetRowCombination sample A = 0 ↔
      ∀ b : Fin (4 * r),
        ColumnParityZero A (sampleEquivGrouped r sample b) := by sorry
