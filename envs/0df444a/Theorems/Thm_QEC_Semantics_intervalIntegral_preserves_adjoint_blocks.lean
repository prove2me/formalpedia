-- Prove2me | Theorems.Thm_QEC_Semantics_intervalIntegral_preserves_adjoint_blocks
-- name    : QEC.Semantics.intervalIntegral_preserves_adjoint_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:00.378639+00:00
-- url     : https://prove2.me/theorems/9532dd87-2652-4b11-a042-acf00d2b5edf
-- title:
--   Semantics: interval Integral preserves adjoint blocks
-- statement:
--   The Semantics construction uses the interval Integral preserves adjoint blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L931-L974
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L931-L974

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
set_option maxHeartbeats 800000

theorem QEC.Semantics.intervalIntegral_preserves_adjoint_blocks
    (f : Real → ContinuousSuperoperator H) (a b : Real)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hab : a ≤ b) (A B : Operator H)
    (hsym : ∀ s ∈ Set.Icc a b, asOperatorSuperoperator (f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (f s) A)) :
    asOperatorSuperoperator (∫ s in a..b, f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (∫ s in a..b, f s) A) := by sorry
