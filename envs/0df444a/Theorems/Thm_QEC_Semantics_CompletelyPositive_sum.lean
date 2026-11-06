-- Prove2me | Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
-- name    : QEC.Semantics.CompletelyPositive.sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:59:54.470051+00:00
-- url     : https://prove2.me/theorems/f9d0f11a-0539-411e-94dc-aa9e19230ce0
-- title:
--   Completely Positive: sum
-- statement:
--   The Completely Positive construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L358-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L358-L363

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
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.CompletelyPositive.sum {κ : Type*} [Fintype κ]
    {Φ : κ → Operator H →ₗ[Complex] Operator K}
    (hΦ : ∀ i, CompletelyPositive (Φ i)) :
    CompletelyPositive (∑ i, Φ i) := by sorry
