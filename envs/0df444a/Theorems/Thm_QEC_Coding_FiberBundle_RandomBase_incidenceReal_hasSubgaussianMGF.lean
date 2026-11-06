-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_incidenceReal_hasSubgaussianMGF
-- name    : QEC.Coding.FiberBundle.RandomBase.incidenceReal_hasSubgaussianMGF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:06.3022+00:00
-- url     : https://prove2.me/theorems/7796dc9f-5d68-409f-9f17-4859014f0085
-- title:
--   Random Base: incidence Real has Subgaussian MGF
-- statement:
--   One centered incidence indicator is sub-Gaussian with Hoeffding parameter
--   `1/4`.  The centering constant is computed from the sampled Bernoulli law,
--   not supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L250-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L250-L269

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

theorem QEC.Coding.FiberBundle.RandomBase.incidenceReal_hasSubgaussianMGF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun sample =>
        incidenceReal edge sample -
          (incidenceProbability (4 * r) Delta).toReal)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by sorry
