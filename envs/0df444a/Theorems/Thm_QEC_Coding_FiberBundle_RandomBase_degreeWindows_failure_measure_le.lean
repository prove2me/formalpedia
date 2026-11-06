-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_degreeWindows_failure_measure_le
-- name    : QEC.Coding.FiberBundle.RandomBase.degreeWindows_failure_measure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:25.087461+00:00
-- url     : https://prove2.me/theorems/31f28829-c228-4581-af3c-639370accc3e
-- title:
--   Random Base: degree Windows failure measure le
-- statement:
--   Union bound for the full HHO20 degree-window event.  There are exactly
--   `2(3r) + 2(4r) = 14r` atomic bad events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1004-L1022
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1004-L1022

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

theorem QEC.Coding.FiberBundle.RandomBase.degreeWindows_failure_measure_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ¬HasDegreeWindows (Delta := Delta) sample} ≤
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) := by sorry
