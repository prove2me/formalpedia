-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_erasureCorrectable_iff
-- name    : QEC.Semantics.FiniteSubsystem.erasureCorrectable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:48.355708+00:00
-- url     : https://prove2.me/theorems/b4e56d28-0fb5-4375-88e6-d273552c4ffd
-- title:
--   Finite Subsystem: erasure Correctable iff
-- statement:
--   Erasure correctability is definitionally the existing M2 `Correctable` predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L350-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L350-L354

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

theorem QEC.Semantics.FiniteSubsystem.erasureCorrectable_iff (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by sorry
