-- Prove2me | Theorems.Thm_QEC_Semantics_hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
-- name    : QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:36.630995+00:00
-- url     : https://prove2.me/theorems/2e58060b-dcba-458b-b954-dd4f6ef99b15
-- title:
--   Semantics: has Deriv At lindblad No Jump Trajectory Continuous raw
-- statement:
--   The Semantics construction uses the has Deriv At lindblad No Jump Trajectory Continuous raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L574-L584
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L574-L584

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete

theorem QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    HasDerivAt (lindbladNoJumpTrajectoryContinuous K A)
      (((lindbladNoJumpPropagatorContinuous K t *
          LinearMap.toContinuousLinearMap K) * A) *
          ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) +
        (lindbladNoJumpPropagatorContinuous K t * A) *
          (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
            ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) t := by sorry
