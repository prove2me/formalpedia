-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
-- name    : QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:09.712315+00:00
-- url     : https://prove2.me/theorems/4732d224-7d9d-4731-842b-f5a1525d1efa
-- title:
--   Random Base: grouped Distribution apply
-- statement:
--   The Random Base construction uses the grouped Distribution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L68-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L68-L76

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

theorem QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (grouped : GroupedSample r) :
    groupedDistribution r Delta hDelta grouped =
      ∏ b : Fin (4 * r), ∏ a : Fin (3 * r),
        cond (grouped b a)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by sorry
