-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
-- name    : QEC.Semantics.QuditSubsystem.registerFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:11:09.086221+00:00
-- url     : https://prove2.me/theorems/1f11b655-e189-4b8c-be0c-d99c50ba84fe
-- title:
--   Qudit Subsystem: register Factorization apply basis
-- statement:
--   Factorization maps every global basis vector to its selected/complement tensor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L233-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L233-L242

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

theorem QEC.Semantics.QuditSubsystem.registerFactorization_apply_basis (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.registerFactorization (EuclideanSpace.basisFun (Qudit.Label q) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
        (S.splitLabel labels).2) := by sorry
