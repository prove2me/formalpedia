-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
-- name    : QEC.Semantics.QuditSubsystem.conjOperator_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:10:00.411305+00:00
-- url     : https://prove2.me/theorems/d469ce80-023a-437d-9f59-fc7a99a0f712
-- title:
--   Qudit Subsystem: conj Operator rank One
-- statement:
--   Unitary conjugation sends a rank-one operator to the corresponding transported rank one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L87-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L87-L98

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

theorem QEC.Semantics.QuditSubsystem.conjOperator_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (x y : H) :
    U.conjOperator (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (InnerProductSpace.rankOne Complex (U x) (U y)).toLinearMap := by sorry
