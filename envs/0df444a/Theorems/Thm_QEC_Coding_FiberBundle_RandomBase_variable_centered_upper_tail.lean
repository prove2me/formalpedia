-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_variable_centered_upper_tail
-- name    : QEC.Coding.FiberBundle.RandomBase.variable_centered_upper_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:33:46.036548+00:00
-- url     : https://prove2.me/theorems/8a5a7b1f-1841-4a58-848e-a23f9b7f01f8
-- title:
--   Random Base: variable centered upper tail
-- statement:
--   Hoeffding upper tail for one variable degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L724-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L724-L751

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

theorem QEC.Coding.FiberBundle.RandomBase.variable_centered_upper_tail
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ε ≤ ∑ a : Fin (3 * r),
            (incidenceReal (a, b) sample -
              (incidenceProbability (4 * r) Delta).toReal)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _a : Fin (3 * r), ((1 / 4 : NNReal) : Real))) := by sorry
