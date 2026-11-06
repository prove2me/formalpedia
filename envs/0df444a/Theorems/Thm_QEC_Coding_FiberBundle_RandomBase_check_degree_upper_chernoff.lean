-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_upper_chernoff
-- name    : QEC.Coding.FiberBundle.RandomBase.check_degree_upper_chernoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:32:34.291828+00:00
-- url     : https://prove2.me/theorems/28fdec0f-502c-40fa-a1ff-4b2d763b45a4
-- title:
--   Random Base: check degree upper chernoff
-- statement:
--   Chernoff upper tail for one check degree, before optimizing `t`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L491-L507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L491-L507

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

theorem QEC.Coding.FiberBundle.RandomBase.check_degree_upper_chernoff
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε t : Real) (ht : 0 ≤ t) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (checkDegree sample a : Real)} ≤
      Real.exp (-t * ε + (Delta : Real) * (Real.exp t - 1)) := by sorry
