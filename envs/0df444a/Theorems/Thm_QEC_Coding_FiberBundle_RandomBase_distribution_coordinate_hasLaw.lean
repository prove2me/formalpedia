-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_coordinate_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_coordinate_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:37.082495+00:00
-- url     : https://prove2.me/theorems/df63ae37-12b9-44e6-ae25-ab403249916f
-- title:
--   Random Base: distribution coordinate has Law
-- statement:
--   Each sampled incidence has the exact Bernoulli law `Delta / (4r)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L162-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L162-L177

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

theorem QEC.Coding.FiberBundle.RandomBase.distribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun sample : Sample r => sample edge)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (distribution r Delta hDelta).toMeasure := by sorry
