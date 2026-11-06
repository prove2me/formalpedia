-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_toMeasure_eq_pi
-- name    : QEC.Coding.FiberBundle.RandomBase.independentProduct_toMeasure_eq_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:46.819516+00:00
-- url     : https://prove2.me/theorems/ad0aa9ab-abaf-4cda-a0ab-f651b4591526
-- title:
--   Random Base: independent Product to Measure eq pi
-- statement:
--   The measure induced by the finite independent-product PMF is Mathlib's product
--   measure of the coordinate PMFs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L62-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L62-L82

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

theorem QEC.Coding.FiberBundle.RandomBase.independentProduct_toMeasure_eq_pi
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) :
    (independentProduct p).toMeasure =
      Measure.pi (fun i => (p i).toMeasure) := by sorry
