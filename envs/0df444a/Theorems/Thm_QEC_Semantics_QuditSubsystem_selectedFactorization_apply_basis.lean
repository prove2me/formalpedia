-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedFactorization_apply_basis
-- name    : QEC.Semantics.QuditSubsystem.selectedFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:25:42.733493+00:00
-- url     : https://prove2.me/theorems/2a4a5fbe-9db8-4099-9e7c-a31fbbcc2eac
-- title:
--   Qudit Subsystem: selected Factorization apply basis
-- statement:
--   The selected-factorization maps each selected label of `T` to its `S` and `T \ S` factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L652-L663
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L652-L663

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

theorem QEC.Semantics.QuditSubsystem.selectedFactorization_apply_basis (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label T.selectedDimensions) :
    S.selectedFactorization T hST
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitSelectedLabel T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
        (S.splitSelectedLabel T hST labels).2) := by sorry
