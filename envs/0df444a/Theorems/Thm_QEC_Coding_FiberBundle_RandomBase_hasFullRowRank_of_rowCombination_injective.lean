-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasFullRowRank_of_rowCombination_injective
-- name    : QEC.Coding.FiberBundle.RandomBase.hasFullRowRank_of_rowCombination_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:40.797062+00:00
-- url     : https://prove2.me/theorems/30b5b9ea-aa3d-4411-82c7-e8242d07e8d7
-- title:
--   Random Base: has Full Row Rank of row Combination injective
-- statement:
--   Injectivity of row combinations is equivalent to the needed row independence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1051-L1058
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1051-L1058

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

theorem QEC.Coding.FiberBundle.RandomBase.hasFullRowRank_of_rowCombination_injective
    {r : Nat} {sample : Sample r}
    (hinj : Function.Injective fun coeff : Fin (3 * r) → ZMod 2 =>
      rowCombination sample coeff) :
    HasFullRowRank sample := by sorry
