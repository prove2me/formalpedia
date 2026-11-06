-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_eq_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:37:01.336322+00:00
-- url     : https://prove2.me/theorems/70461afa-b790-4d33-a46b-2061b0418cd2
-- title:
--   Random Base: event Mass eq to Measure
-- statement:
--   `eventMass` is the PMF measure of the represented finite event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1098-L1108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1098-L1108

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

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_eq_toMeasure
    {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] :
    eventMass p event = p.toMeasure {ω | event ω} := by sorry
