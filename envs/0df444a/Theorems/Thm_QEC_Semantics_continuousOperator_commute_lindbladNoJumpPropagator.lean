-- Prove2me | Theorems.Thm_QEC_Semantics_continuousOperator_commute_lindbladNoJumpPropagator
-- name    : QEC.Semantics.continuousOperator_commute_lindbladNoJumpPropagator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:34.181456+00:00
-- url     : https://prove2.me/theorems/ec2cd6c7-787e-4026-983b-356400e2e360
-- title:
--   Semantics: continuous Operator commute lindblad No Jump Propagator
-- statement:
--   The Semantics construction uses the continuous Operator commute lindblad No Jump Propagator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L586-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L586-L592

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

theorem QEC.Semantics.continuousOperator_commute_lindbladNoJumpPropagator
    (K : Operator H) (t : Real) :
    Commute (LinearMap.toContinuousLinearMap K)
      (lindbladNoJumpPropagatorContinuous K t) := by sorry
