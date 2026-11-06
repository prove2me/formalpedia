-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomBase.independentProduct_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:05.31697+00:00
-- url     : https://prove2.me/theorems/54d7b2fe-385d-432c-b407-d3bd643a9599
-- title:
--   Random Base: independent Product i Indep Fun
-- statement:
--   Coordinate projections are independent under the measure induced by
--   `independentProduct`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L88-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L88-L97

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

theorem QEC.Coding.FiberBundle.RandomBase.independentProduct_iIndepFun
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) :
    ProbabilityTheory.iIndepFun
      (fun i x => x i) (independentProduct p).toMeasure := by sorry
