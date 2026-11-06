-- Prove2me | Theorems.Thm_QEC_Semantics_hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous
-- name    : QEC.Semantics.hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:59:08.004108+00:00
-- url     : https://prove2.me/theorems/2a145d40-c8c0-4094-b378-8b5e74a5a901
-- title:
--   Semantics: has Deriv At adjoint lindblad No Jump Propagator Continuous
-- statement:
--   The Semantics construction uses the has Deriv At adjoint lindblad No Jump Propagator Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L543-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L543-L565

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

theorem QEC.Semantics.hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) :
    HasDerivAt
      (fun s : Real =>
        ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K s))
      (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by sorry
