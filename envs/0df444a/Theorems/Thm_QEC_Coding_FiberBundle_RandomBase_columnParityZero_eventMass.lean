-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnParityZero_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.columnParityZero_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:29:43.566597+00:00
-- url     : https://prove2.me/theorems/e9c9f1c9-0070-4364-85e2-b6cbb910acad
-- title:
--   Random Base: column Parity Zero event Mass
-- statement:
--   ENNReal event-mass form of the exact one-column parity formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L411-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L411-L429

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

theorem QEC.Coding.FiberBundle.RandomBase.columnParityZero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by sorry
