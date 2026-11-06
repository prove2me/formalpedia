-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:12:18.71582+00:00
-- url     : https://prove2.me/theorems/a27ed768-4e4a-49c3-a55d-6d17063f624e
-- title:
--   Qudit Subsystem: erasure Channel From Register rank One basis
-- statement:
--   Erasure contracts the selected components of global computational matrix units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L486-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L486-L505

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

theorem QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_rankOne_basis (S : QuditSubsystem q)
    (x y : Qudit.Label q) :
    S.erasureChannelFromRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label q) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2)).toLinearMap := by sorry
