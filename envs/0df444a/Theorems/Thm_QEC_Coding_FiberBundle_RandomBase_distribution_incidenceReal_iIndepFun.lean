-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_incidenceReal_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomBase.distribution_incidenceReal_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:46.483788+00:00
-- url     : https://prove2.me/theorems/f433c4f8-f5dc-40bd-add9-bb90c807db0c
-- title:
--   Random Base: distribution incidence Real i Indep Fun
-- statement:
--   The real incidence indicators remain mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L186-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L186-L193

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

theorem QEC.Coding.FiberBundle.RandomBase.distribution_incidenceReal_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge => incidenceReal edge)
      (distribution r Delta hDelta).toMeasure := by sorry
