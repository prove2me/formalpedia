-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_nonempty_finset_pow_card
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_nonempty_finset_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:30:23.563309+00:00
-- url     : https://prove2.me/theorems/72e45a7b-652b-4578-8d9e-447e03128e0f
-- title:
--   Random Base: sum nonempty finset pow card
-- statement:
--   The nonempty subsets contribute the binomial sum with its empty-set term
--   removed.  This is the counting identity needed by the rank union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L693-L725
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L693-L725

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

theorem QEC.Coding.FiberBundle.RandomBase.sum_nonempty_finset_pow_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (t : ENNReal) :
    (∑ A : {A : Finset α // A.Nonempty}, t ^ A.1.card) =
      (1 + t) ^ Fintype.card α - 1 := by sorry
