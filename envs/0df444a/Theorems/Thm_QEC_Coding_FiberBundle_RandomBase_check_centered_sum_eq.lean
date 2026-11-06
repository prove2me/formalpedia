-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_centered_sum_eq
-- name    : QEC.Coding.FiberBundle.RandomBase.check_centered_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:30:29.324767+00:00
-- url     : https://prove2.me/theorems/a1726b1d-8df7-4427-b109-396ecc450c4b
-- title:
--   Random Base: check centered sum eq
-- statement:
--   Rewrite a centered check-incidence sum as degree minus its exact mean.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L330-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L330-L340

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

theorem QEC.Coding.FiberBundle.RandomBase.check_centered_sum_eq
    (r Delta : Nat) (hr : 0 < r)
    (sample : Sample r) (a : Fin (3 * r)) :
    (∑ b : Fin (4 * r),
        (incidenceReal (a, b) sample -
          (incidenceProbability (4 * r) Delta).toReal)) =
      (checkDegree sample a : Real) - Delta := by sorry
