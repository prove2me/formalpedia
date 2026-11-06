-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_degreeWindows_failureMass_le
-- name    : QEC.Coding.FiberBundle.RandomBase.degreeWindows_failureMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:37:39.945604+00:00
-- url     : https://prove2.me/theorems/b986f1cd-ec2d-4d47-a4b7-03c9c4f7de15
-- title:
--   Random Base: degree Windows failure Mass le
-- statement:
--   ENNReal form of the global degree-window failure bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1130-L1145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L1130-L1145

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

theorem QEC.Coding.FiberBundle.RandomBase.degreeWindows_failureMass_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    @failureMass
        (Sample r)
        inferInstance
        (distribution r Delta hDelta)
        (fun sample => HasDegreeWindows (Delta := Delta) sample)
        (Classical.decPred _) ≤
      ENNReal.ofReal
        ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) := by sorry
