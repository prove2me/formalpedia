-- Prove2me | Theorems.Thm_QEC_Semantics_asOperatorSuperoperator_finset_sum
-- name    : QEC.Semantics.asOperatorSuperoperator_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:44.17966+00:00
-- url     : https://prove2.me/theorems/e3751d47-4994-48f9-b7a6-2829f9603421
-- title:
--   Semantics: as Operator Superoperator finset sum
-- statement:
--   The Semantics construction uses the as Operator Superoperator finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L752-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L752-L758

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

theorem QEC.Semantics.asOperatorSuperoperator_finset_sum {κ : Type*}
    (s : Finset κ) (f : κ → ContinuousSuperoperator H) :
    asOperatorSuperoperator (∑ i ∈ s, f i) =
      ∑ i ∈ s, asOperatorSuperoperator (f i) := by sorry
