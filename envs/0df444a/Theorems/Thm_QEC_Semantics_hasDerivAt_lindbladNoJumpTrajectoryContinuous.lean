-- Prove2me | Theorems.Thm_QEC_Semantics_hasDerivAt_lindbladNoJumpTrajectoryContinuous
-- name    : QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:00:01.59641+00:00
-- url     : https://prove2.me/theorems/8f3d8e72-8857-4308-9900-455e02fdc593
-- title:
--   Semantics: has Deriv At lindblad No Jump Trajectory Continuous
-- statement:
--   The Semantics construction uses the has Deriv At lindblad No Jump Trajectory Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L594-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L594-L603

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

theorem QEC.Semantics.hasDerivAt_lindbladNoJumpTrajectoryContinuous
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    HasDerivAt (lindbladNoJumpTrajectoryContinuous K A)
      (LinearMap.toContinuousLinearMap K *
          lindbladNoJumpTrajectoryContinuous K A t +
        lindbladNoJumpTrajectoryContinuous K A t *
          ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by sorry
