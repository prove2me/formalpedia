-- Prove2me | Theorems.Thm_QEC_Semantics_continuous_lindbladDysonIntegrandContinuous
-- name    : QEC.Semantics.continuous_lindbladDysonIntegrandContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:46.498801+00:00
-- url     : https://prove2.me/theorems/b4cc3875-5dcf-4f15-8acd-6f1df1501006
-- title:
--   Semantics: continuous lindblad Dyson Integrand Continuous
-- statement:
--   The Semantics construction uses the continuous lindblad Dyson Integrand Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L881-L888
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L881-L888

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

theorem QEC.Semantics.continuous_lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H)
    (hprevious : Continuous previous) (t : Real) :
    Continuous (lindbladDysonIntegrandContinuous K J previous t) := by sorry
