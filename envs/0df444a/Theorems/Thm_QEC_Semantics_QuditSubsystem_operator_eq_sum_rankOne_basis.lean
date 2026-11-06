-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:11:05.937442+00:00
-- url     : https://prove2.me/theorems/9bca242f-69b9-4d26-aaaa-d4b3bb76d56b
-- title:
--   Qudit Subsystem: operator eq sum rank One basis
-- statement:
--   Expand an arbitrary finite-dimensional operator in rank-one matrix units for an orthonormal basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L101-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L101-L120

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_basis (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ,
      (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by sorry
