-- Prove2me | Theorems.Thm_QEC_Semantics_CompletelyPositive_intervalIntegral
-- name    : QEC.Semantics.CompletelyPositive.intervalIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:26:46.717882+00:00
-- url     : https://prove2.me/theorems/53f4ca96-71f5-44ae-a0cb-647cbab81188
-- title:
--   Completely Positive: interval Integral
-- statement:
--   The Completely Positive construction uses the interval Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1067-L1085
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1067-L1085

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
open QEC.Semantics.CompletelyPositive
set_option maxHeartbeats 800000

theorem QEC.Semantics.CompletelyPositive.intervalIntegral
    (f : Real → ContinuousSuperoperator H) (a b : Real) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hcp : ∀ s ∈ Set.Icc a b,
      CompletelyPositive (asOperatorSuperoperator (f s))) :
    CompletelyPositive (asOperatorSuperoperator (∫ s in a..b, f s)) := by sorry
