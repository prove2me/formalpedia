-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:08.934879+00:00
-- url     : https://prove2.me/theorems/1717de50-fb2f-4fc5-92c1-46089bbe2ab6
-- title:
--   Random Base: subset Row Combination zero event Mass
-- statement:
--   Exact probability mass that a fixed row subset sums to zero in every column:
--   the paper's `q_w^(4r)` formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L457-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L457-L495

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

theorem QEC.Coding.FiberBundle.RandomBase.subsetRowCombination_zero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (3 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => subsetRowCombination sample A = 0) =
      (ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2)) ^
        (4 * r) := by sorry
