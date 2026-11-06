-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_symm_apply_basis
-- name    : QEC.Semantics.QuditSubsystem.registerFactorization_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:40.56072+00:00
-- url     : https://prove2.me/theorems/7a052409-1aab-445d-ae47-bdf4d9ee54f1
-- title:
--   Qudit Subsystem: register Factorization symm apply basis
-- statement:
--   Recombination maps a selected/complement basis tensor back to its global basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L256-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L256-L266

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

theorem QEC.Semantics.QuditSubsystem.registerFactorization_symm_apply_basis (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.registerFactorization.symm
        ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex labels.1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label q) Complex (S.recombineLabel labels) := by sorry
