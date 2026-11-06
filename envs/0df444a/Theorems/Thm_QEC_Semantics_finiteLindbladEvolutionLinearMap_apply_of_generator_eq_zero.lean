-- Prove2me | Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_apply_of_generator_eq_zero
-- name    : QEC.Semantics.finiteLindbladEvolutionLinearMap_apply_of_generator_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:03:17.930468+00:00
-- url     : https://prove2.me/theorems/ed97db5e-6f72-4d24-9447-241136ac0878
-- title:
--   Semantics: finite Lindblad Evolution Linear Map apply of generator eq zero
-- statement:
--   The Semantics construction uses the finite Lindblad Evolution Linear Map apply of generator eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1500-L1509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Lindblad.lean#L1500-L1509

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

theorem QEC.Semantics.finiteLindbladEvolutionLinearMap_apply_of_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H)
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (t : Real) :
    finiteLindbladEvolutionLinearMap hamiltonian J t A = A := by sorry
