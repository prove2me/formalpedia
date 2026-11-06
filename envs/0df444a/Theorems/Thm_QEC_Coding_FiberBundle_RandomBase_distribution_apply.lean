-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:28:37.12624+00:00
-- url     : https://prove2.me/theorems/fe13b63b-9919-41a3-b354-efa182bffd21
-- title:
--   Random Base: distribution apply
-- statement:
--   The Random Base construction uses the distribution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L142-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L142-L151

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u

theorem QEC.Coding.FiberBundle.RandomBase.distribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (sample : Sample r) :
    distribution r Delta hDelta sample =
      ∏ edge : Fin (3 * r) × Fin (4 * r),
        cond (sample edge)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by sorry
