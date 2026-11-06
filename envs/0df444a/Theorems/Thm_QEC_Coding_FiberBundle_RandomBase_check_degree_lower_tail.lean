-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_lower_tail
-- name    : QEC.Coding.FiberBundle.RandomBase.check_degree_lower_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:36:04.697208+00:00
-- url     : https://prove2.me/theorems/be0f3d4b-ccf8-44a0-b9c9-622f9a9d30e0
-- title:
--   Random Base: check degree lower tail
-- statement:
--   Lower-tail form stated directly for a check degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L799-L822
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L799-L822

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

theorem QEC.Coding.FiberBundle.RandomBase.check_degree_lower_tail
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (Delta : Real) - checkDegree sample a} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _b : Fin (4 * r), ((1 / 4 : NNReal) : Real))) := by sorry
