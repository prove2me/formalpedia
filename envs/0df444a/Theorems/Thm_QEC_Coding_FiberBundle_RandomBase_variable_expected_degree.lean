-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_variable_expected_degree
-- name    : QEC.Coding.FiberBundle.RandomBase.variable_expected_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:30:41.695068+00:00
-- url     : https://prove2.me/theorems/115c57d3-09c0-45ec-bd87-448769b343ad
-- title:
--   Random Base: variable expected degree
-- statement:
--   The expected variable degree is exactly `3 Delta / 4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L320-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L320-L327

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

theorem QEC.Coding.FiberBundle.RandomBase.variable_expected_degree
    (r Delta : Nat) (hr : 0 < r) :
    ((3 * r : Nat) : Real) *
        (incidenceProbability (4 * r) Delta).toReal =
      3 * (Delta : Real) / 4 := by sorry
