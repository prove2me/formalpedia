-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:26.983552+00:00
-- url     : https://prove2.me/theorems/f894f5d6-8504-4fdb-8f0c-6ed5075e9d2d
-- title:
--   Random Base: distribution i Indep Fun
-- statement:
--   Every Tanner incidence coordinate is independent under the random-base measure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L154-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L154-L159

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

theorem QEC.Coding.FiberBundle.RandomBase.distribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge (sample : Sample r) => sample edge)
      (distribution r Delta hDelta).toMeasure := by sorry
