-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_sub_one_le_add_sq
-- name    : QEC.Coding.FiberBundle.RandomBase.exp_sub_one_le_add_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:25.607434+00:00
-- url     : https://prove2.me/theorems/330a38b4-45a0-4d1f-a54a-33f1252b0879
-- title:
--   Random Base: exp sub one le add sq
-- statement:
--   A convenient second-order upper bound for the exponential function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L485-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L485-L488

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

theorem QEC.Coding.FiberBundle.RandomBase.exp_sub_one_le_add_sq {t : Real} (ht : |t| ≤ 1) :
    Real.exp t - 1 ≤ t + t ^ 2 := by sorry
