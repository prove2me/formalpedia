-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply_eq_grouped
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_apply_eq_grouped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:08.703954+00:00
-- url     : https://prove2.me/theorems/6db6841a-95e9-4e3e-b7a1-4bbf9182a473
-- title:
--   Random Base: distribution apply eq grouped
-- statement:
--   Regrouping changes no probability mass.  This is an exact equality of PMFs,
--   not an independence assumption about the sampled matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L108-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L108-L118

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

theorem QEC.Coding.FiberBundle.RandomBase.distribution_apply_eq_grouped
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      groupedDistribution r Delta hDelta (sampleEquivGrouped r sample) := by sorry
