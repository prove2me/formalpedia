-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree
-- name    : QEC.Coding.FiberBundle.RandomBase.check_expected_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:30.667193+00:00
-- url     : https://prove2.me/theorems/be82873e-d91d-4df8-a9a6-89f68d0ae4bd
-- title:
--   Random Base: check expected degree
-- statement:
--   The expected check degree is exactly `Delta`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L311-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L311-L317

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

theorem QEC.Coding.FiberBundle.RandomBase.check_expected_degree
    (r Delta : Nat) (hr : 0 < r) :
    ((4 * r : Nat) : Real) *
        (incidenceProbability (4 * r) Delta).toReal =
      Delta := by sorry
