-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkDegree_cast_eq_sum_incidenceReal
-- name    : QEC.Coding.FiberBundle.RandomBase.checkDegree_cast_eq_sum_incidenceReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:30:23.071921+00:00
-- url     : https://prove2.me/theorems/5cbc8674-2266-442c-a97b-fc65bea1f845
-- title:
--   Random Base: check Degree cast eq sum incidence Real
-- statement:
--   A check degree is the sum of its real incidence indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L297-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L297-L301

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

theorem QEC.Coding.FiberBundle.RandomBase.checkDegree_cast_eq_sum_incidenceReal
    {r : Nat} (sample : Sample r) (a : Fin (3 * r)) :
    (checkDegree sample a : Real) =
      ∑ b : Fin (4 * r), incidenceReal (a, b) sample := by sorry
