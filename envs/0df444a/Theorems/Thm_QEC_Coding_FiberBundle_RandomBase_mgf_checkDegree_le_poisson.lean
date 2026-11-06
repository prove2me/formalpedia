-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mgf_checkDegree_le_poisson
-- name    : QEC.Coding.FiberBundle.RandomBase.mgf_checkDegree_le_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:02.594214+00:00
-- url     : https://prove2.me/theorems/c3ebcb29-4af9-4fe7-b8af-21e8bb3b03a3
-- title:
--   Random Base: mgf check Degree le poisson
-- statement:
--   Poisson-envelope MGF bound for one check degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L427-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean#L427-L453

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

theorem QEC.Coding.FiberBundle.RandomBase.mgf_checkDegree_le_poisson
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample => (checkDegree sample a : Real))
        (distribution r Delta hDelta).toMeasure
        t ≤
      Real.exp ((Delta : Real) * (Real.exp t - 1)) := by sorry
