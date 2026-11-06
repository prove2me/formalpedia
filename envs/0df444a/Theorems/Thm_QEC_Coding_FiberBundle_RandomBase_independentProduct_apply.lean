-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
-- name    : QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:28:44.008202+00:00
-- url     : https://prove2.me/theorems/1f2cf76f-dd0e-4496-9990-a4d19f588580
-- title:
--   Random Base: independent Product apply
-- statement:
--   The Random Base construction uses the independent Product apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L51-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L51-L56

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

theorem QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i)) (x : ∀ i, κ i) :
    independentProduct p x = ∏ i, p i (x i) := by sorry

attribute [defeq] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
