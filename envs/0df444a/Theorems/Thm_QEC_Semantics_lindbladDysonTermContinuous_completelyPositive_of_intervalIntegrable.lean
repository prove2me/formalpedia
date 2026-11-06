-- Prove2me | Theorems.Thm_QEC_Semantics_lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable
-- name    : QEC.Semantics.lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:21.275079+00:00
-- url     : https://prove2.me/theorems/d056275f-b961-4302-9f9a-777c41713dcd
-- title:
--   Semantics: lindblad Dyson Term Continuous completely Positive of interval Integrable
-- statement:
--   The Semantics construction uses the lindblad Dyson Term Continuous completely Positive of interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1185-L1205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1185-L1205

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

theorem QEC.Semantics.lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable
    [Fintype ι] (K : Operator H) (J : ι → Operator H)
    (hintegrable : ∀ n t, IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t)
    (n : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J n t)) := by sorry
