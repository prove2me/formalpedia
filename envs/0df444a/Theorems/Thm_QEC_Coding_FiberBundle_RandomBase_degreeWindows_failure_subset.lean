-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_degreeWindows_failure_subset
-- name    : QEC.Coding.FiberBundle.RandomBase.degreeWindows_failure_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:17.256233+00:00
-- url     : https://prove2.me/theorems/907591bb-2754-4e9d-986a-0a11c39812a4
-- title:
--   Random Base: degree Windows failure subset
-- statement:
--   Failure of the global degree windows is covered by the atomic bad events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L975-L998
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L975-L998

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

theorem QEC.Coding.FiberBundle.RandomBase.degreeWindows_failure_subset
    (r Delta : Nat) :
    {sample : Sample r | ¬HasDegreeWindows (Delta := Delta) sample} ⊆
      ⋃ i : DegreeFailureIndex r, degreeFailureEvent r Delta i := by sorry
