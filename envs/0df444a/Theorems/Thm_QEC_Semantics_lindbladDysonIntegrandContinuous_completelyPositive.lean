-- Prove2me | Theorems.Thm_QEC_Semantics_lindbladDysonIntegrandContinuous_completelyPositive
-- name    : QEC.Semantics.lindbladDysonIntegrandContinuous_completelyPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:46.825171+00:00
-- url     : https://prove2.me/theorems/d03df44a-d040-4d23-be3f-eaa8790c7b94
-- title:
--   Semantics: lindblad Dyson Integrand Continuous completely Positive
-- statement:
--   The Semantics construction uses the lindblad Dyson Integrand Continuous completely Positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L845-L858
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L845-L858

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

theorem QEC.Semantics.lindbladDysonIntegrandContinuous_completelyPositive [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H)
    (t s : Real)
    (hprevious : CompletelyPositive (asOperatorSuperoperator (previous s))) :
    CompletelyPositive
      (asOperatorSuperoperator
        (lindbladDysonIntegrandContinuous K J previous t s)) := by sorry
