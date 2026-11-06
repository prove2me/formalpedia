-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fullRowRank_failureMass_le_split
-- name    : QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:30:59.992814+00:00
-- url     : https://prove2.me/theorems/97e95daf-7c73-4647-b012-ac2a6ee3eb81
-- title:
--   Random Base: full Row Rank failure Mass le split
-- statement:
--   The rank-failure union bound after the HHO20 small/large subset split.
--
--   The first summand is the exact binomial contribution of all nonempty
--   small-subset geometric weights.  The second summand bounds the number of
--   large subsets by all `2^(3r)` row subsets.  No independence between distinct
--   row-dependency events is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L781-L834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L781-L834

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

theorem QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_split
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      (1 + ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
      (2 : ENNReal) ^ (3 * r) *
        (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r) := by sorry
