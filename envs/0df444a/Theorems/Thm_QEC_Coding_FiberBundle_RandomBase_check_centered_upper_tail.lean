-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_centered_upper_tail
-- name    : QEC.Coding.FiberBundle.RandomBase.check_centered_upper_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:33:46.161607+00:00
-- url     : https://prove2.me/theorems/68e95c15-ae74-42a1-af31-5a467c63766b
-- title:
--   Random Base: check centered upper tail
-- statement:
--   Hoeffding upper tail for one check degree, expressed as the exact sum of
--   centered incidence indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L658-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L658-L685

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

theorem QEC.Coding.FiberBundle.RandomBase.check_centered_upper_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ b : Fin (4 * r),
            (incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by sorry
