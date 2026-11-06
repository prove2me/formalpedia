-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_powerset_pow_card
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_powerset_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:54.580404+00:00
-- url     : https://prove2.me/theorems/97ec2579-cc0f-47f2-8ec1-566c9b1f2376
-- title:
--   Random Base: sum powerset pow card
-- statement:
--   Binomial enumeration of subsets, with the subset weight left symbolic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L681-L687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L681-L687

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

theorem QEC.Coding.FiberBundle.RandomBase.sum_powerset_pow_card
    {α : Type*} [DecidableEq α]
    (s : Finset α) (t : ENNReal) :
    ∑ A ∈ s.powerset, t ^ A.card = (1 + t) ^ s.card := by sorry
