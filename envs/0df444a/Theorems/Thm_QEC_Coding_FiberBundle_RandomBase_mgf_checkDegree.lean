-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mgf_checkDegree
-- name    : QEC.Coding.FiberBundle.RandomBase.mgf_checkDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:43.449191+00:00
-- url     : https://prove2.me/theorems/439a5621-ea06-4186-801a-93ca4d1b0deb
-- title:
--   Random Base: mgf check Degree
-- statement:
--   Exact MGF of a sampled check degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L356-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L356-L382

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

theorem QEC.Coding.FiberBundle.RandomBase.mgf_checkDegree
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (checkDegree sample a : Real))
        (distribution r Delta hDelta).toMeasure
        t =
      ((1 - (incidenceProbability (4 * r) Delta).toReal) +
          (incidenceProbability (4 * r) Delta).toReal * Real.exp t) ^
        (4 * r) := by sorry
