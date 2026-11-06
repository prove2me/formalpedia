-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_coordinate_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomBase.columnDistribution_coordinate_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:25.233576+00:00
-- url     : https://prove2.me/theorems/f79858cd-4f9d-4318-bcf7-4dfe47f1bedf
-- title:
--   Random Base: column Distribution coordinate has Law
-- statement:
--   Every coordinate of a sampled column has the construction's Bernoulli law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L87-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L87-L102

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

theorem QEC.Coding.FiberBundle.RandomBase.columnDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasLaw
      (fun column : ColumnSample r => column a)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (columnDistribution r Delta hDelta).toMeasure := by sorry
