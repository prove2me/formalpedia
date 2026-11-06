-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_symm_apply_basis
-- name    : QEC.Semantics.QuditSubsystem.complementFactorization_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:29.231975+00:00
-- url     : https://prove2.me/theorems/bead2ec3-4c9b-4710-9be6-73462cc1a18b
-- title:
--   Qudit Subsystem: complement Factorization symm apply basis
-- statement:
--   The factorization of the `S` complement recombines its basis labels exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L584-L600
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L584-L600

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

theorem QEC.Semantics.QuditSubsystem.complementFactorization_symm_apply_basis (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions) :
    (S.complementFactorization T hST).symm
        ((EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex labels.1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex labels.2)) =
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
        (S.recombineComplementLabel T labels) := by sorry
