-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_coordinate_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomBase.independentProduct_coordinate_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:15.493418+00:00
-- url     : https://prove2.me/theorems/416f59d1-742e-4d44-b769-398b23e69555
-- title:
--   Random Base: independent Product coordinate has Law
-- statement:
--   Each coordinate projection has exactly its specified coordinate law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L100-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L100-L110

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

theorem QEC.Coding.FiberBundle.RandomBase.independentProduct_coordinate_hasLaw
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) (i : ι) :
    ProbabilityTheory.HasLaw
      (fun x => x i) (p i).toMeasure (independentProduct p).toMeasure := by sorry
