-- Prove2me | Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero
-- name    : QEC.Semantics.finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:29.095877+00:00
-- url     : https://prove2.me/theorems/25be9b67-8848-46f8-a483-c457275133fb
-- title:
--   Semantics: finite Lindblad Evolution Continuous apply of generator eq zero
-- statement:
--   The Semantics construction uses the finite Lindblad Evolution Continuous apply of generator eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1439-L1468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1439-L1468

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

theorem QEC.Semantics.finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H)
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (z : Complex) :
    finiteLindbladEvolutionContinuous hamiltonian J z
      (LinearMap.toContinuousLinearMap A) = LinearMap.toContinuousLinearMap A := by sorry
