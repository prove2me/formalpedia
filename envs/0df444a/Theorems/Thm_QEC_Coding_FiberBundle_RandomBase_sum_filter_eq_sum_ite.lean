-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_filter_eq_sum_ite
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_filter_eq_sum_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:19.11804+00:00
-- url     : https://prove2.me/theorems/8ff0b236-84d2-4c6a-9257-6c78a025b26e
-- title:
--   Random Base: sum filter eq sum ite
-- statement:
--   Rewrite a filtered finite sum as a total sum with an indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L121-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L121-L128

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

theorem QEC.Coding.FiberBundle.RandomBase.sum_filter_eq_sum_ite
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (event : α → Prop) [DecidablePred event]
    (f : α → M) :
    (∑ x ∈ s.filter event, f x) =
      ∑ x ∈ s, if event x then f x else 0 := by sorry
