-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bernoulli_mgf_le_poisson
-- name    : QEC.Coding.FiberBundle.RandomBase.bernoulli_mgf_le_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:02.267217+00:00
-- url     : https://prove2.me/theorems/a03e3fd1-5dff-406e-b9ac-58b897980034
-- title:
--   Random Base: bernoulli mgf le poisson
-- statement:
--   The Bernoulli MGF is bounded by its Poisson envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L414-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L414-L424

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

theorem QEC.Coding.FiberBundle.RandomBase.bernoulli_mgf_le_poisson
    (r Delta : Nat) (t : Real) :
    (1 - (incidenceProbability (4 * r) Delta).toReal) +
        (incidenceProbability (4 * r) Delta).toReal * Real.exp t ≤
      Real.exp
        ((incidenceProbability (4 * r) Delta).toReal *
          (Real.exp t - 1)) := by sorry
