-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_upper_window
-- name    : QEC.Coding.FiberBundle.RandomBase.check_degree_upper_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:32:57.438403+00:00
-- url     : https://prove2.me/theorems/3b4424ab-8551-4247-9b63-ab62e6d88b5e
-- title:
--   Random Base: check degree upper window
-- statement:
--   The HHO20 upper check-degree window has exponentially small failure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L569-L587
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L569-L587

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

theorem QEC.Coding.FiberBundle.RandomBase.check_degree_upper_window
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (101 * (Delta : Real) / 100) ≤ checkDegree sample a} ≤
      Real.exp (-(Delta : Real) / 40000) := by sorry
