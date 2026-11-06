-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_apply_basis
-- name    : QEC.Semantics.QuditSubsystem.complementFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:25:38.397834+00:00
-- url     : https://prove2.me/theorems/1b575d7f-2233-49ac-b1e5-3d23cc2f29cd
-- title:
--   Qudit Subsystem: complement Factorization apply basis
-- statement:
--   The complement factorization maps each `S`-complement basis label to its two factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L570-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L570-L581

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

theorem QEC.Semantics.QuditSubsystem.complementFactorization_apply_basis (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label S.complementDimensions) :
    S.complementFactorization T hST
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
        (S.splitComplementLabel T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
        (S.splitComplementLabel T hST labels).2) := by sorry
