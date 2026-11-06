-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomBase.columnDistribution_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:18.216058+00:00
-- url     : https://prove2.me/theorems/3f007caa-2286-4597-804b-90d7778d10e9
-- title:
--   Random Base: column Distribution i Indep Fun
-- statement:
--   Incidences within one sampled column are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L79-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L79-L84

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

theorem QEC.Coding.FiberBundle.RandomBase.columnDistribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun a (column : ColumnSample r) => column a)
      (columnDistribution r Delta hDelta).toMeasure := by sorry
