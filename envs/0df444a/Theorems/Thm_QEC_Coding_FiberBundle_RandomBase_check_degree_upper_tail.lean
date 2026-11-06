-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_upper_tail
-- name    : QEC.Coding.FiberBundle.RandomBase.check_degree_upper_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:36:17.695462+00:00
-- url     : https://prove2.me/theorems/6a68588a-e3ce-470f-945c-0b00efd5809a
-- title:
--   Random Base: check degree upper tail
-- statement:
--   Upper-tail form stated directly for a check degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L787-L796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L787-L796

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

theorem QEC.Coding.FiberBundle.RandomBase.check_degree_upper_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (checkDegree sample a : Real) - Delta} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by sorry
