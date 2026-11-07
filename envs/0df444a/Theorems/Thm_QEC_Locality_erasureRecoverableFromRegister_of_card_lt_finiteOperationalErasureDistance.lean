-- Prove2me | Theorems.Thm_QEC_Locality_erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
-- name    : QEC.Locality.erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:59.703035+00:00
-- url     : https://prove2.me/theorems/c5f90835-4c4b-4d3e-9ffe-67f0f1df9181
-- title:
--   Locality: erasure Recoverable From Register of card lt finite Operational Erasure Distance
-- statement:
--   Every subsystem smaller than the local convention is recoverable after its concrete erasure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L77-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L77-L85

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.erasureRecoverableFromRegister_of_card_lt_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι)
    (hCard : S.selected.card < finiteOperationalErasureDistance C) :
    S.ErasureRecoverableFromRegister C := by sorry
