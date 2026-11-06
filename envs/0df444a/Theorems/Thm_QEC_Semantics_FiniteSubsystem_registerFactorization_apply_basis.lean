-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
-- name    : QEC.Semantics.FiniteSubsystem.registerFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:11:05.663833+00:00
-- url     : https://prove2.me/theorems/6ff99e64-2687-4a43-af3b-124dbaee643b
-- title:
--   Finite Subsystem: register Factorization apply basis
-- statement:
--   The unitary coordinate factorization maps each global basis label to its selected/complement tensor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L101-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L101-L111

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.registerFactorization_apply_basis (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring ι) :
    S.registerFactorization (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex bits) =
      (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex
        (S.splitBitstring bits).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex
        (S.splitBitstring bits).2) := by sorry
