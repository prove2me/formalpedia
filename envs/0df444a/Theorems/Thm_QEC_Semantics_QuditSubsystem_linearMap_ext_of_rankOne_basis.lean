-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:10:42.376425+00:00
-- url     : https://prove2.me/theorems/6061a29b-dd5a-4917-b6ac-2d0b26fd0de1
-- title:
--   Qudit Subsystem: linear Map ext of rank One basis
-- statement:
--   The Qudit Subsystem construction uses the linear Map ext of rank One basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L124-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L124-L161

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
set_option maxRecDepth 4096

theorem QEC.Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (h : ∀ i j : κ,
      Φ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap =
        Ψ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) : Φ = Ψ := by sorry
