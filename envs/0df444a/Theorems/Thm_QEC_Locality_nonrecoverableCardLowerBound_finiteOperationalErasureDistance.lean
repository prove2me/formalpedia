-- Prove2me | Theorems.Thm_QEC_Locality_nonrecoverableCardLowerBound_finiteOperationalErasureDistance
-- name    : QEC.Locality.nonrecoverableCardLowerBound_finiteOperationalErasureDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:41.120791+00:00
-- url     : https://prove2.me/theorems/71bb6959-75ca-4dac-af74-df9a7b5af8c7
-- title:
--   Locality: nonrecoverable Card Lower Bound finite Operational Erasure Distance
-- statement:
--   A nonrecoverable subsystem has cardinality at least the local convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L65-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L65-L74

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.nonrecoverableCardLowerBound_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (S : Semantics.FiniteSubsystem ι)
    (hS : ¬ S.ErasureRecoverableFromRegister C) :
    finiteOperationalErasureDistance C ≤ S.selected.card := by sorry
