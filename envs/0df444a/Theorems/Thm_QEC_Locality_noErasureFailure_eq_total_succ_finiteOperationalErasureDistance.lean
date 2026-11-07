-- Prove2me | Theorems.Thm_QEC_Locality_noErasureFailure_eq_total_succ_finiteOperationalErasureDistance
-- name    : QEC.Locality.noErasureFailure_eq_total_succ_finiteOperationalErasureDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:12:42.886603+00:00
-- url     : https://prove2.me/theorems/88e39103-0ee6-4ed4-8d8d-f1b7a755a3e1
-- title:
--   Locality: no Erasure Failure eq total succ finite Operational Erasure Distance
-- statement:
--   With no erasure failure, the local convention is capped at `|ι| + 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L54-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L54-L62

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.noErasureFailure_eq_total_succ_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (hRecoverable : ∀ S : Semantics.FiniteSubsystem ι, S.ErasureRecoverableFromRegister C) :
    finiteOperationalErasureDistance C = Fintype.card ι + 1 := by sorry
