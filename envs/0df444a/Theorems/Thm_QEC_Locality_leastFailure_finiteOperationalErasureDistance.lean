-- Prove2me | Theorems.Thm_QEC_Locality_leastFailure_finiteOperationalErasureDistance
-- name    : QEC.Locality.leastFailure_finiteOperationalErasureDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:12:57.215316+00:00
-- url     : https://prove2.me/theorems/14894158-b01e-41ca-b661-18c4ad14fbb8
-- title:
--   Locality: least Failure finite Operational Erasure Distance
-- statement:
--   An extant erasure failure attains the local operational-erasure-distance convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L44-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean#L44-L51

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.leastFailure_finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι))
    (hFailure : ∃ n, FiniteOperationalErasureFailureAt C n) :
    FiniteOperationalErasureFailureAt C (finiteOperationalErasureDistance C) ∧
      ∀ n, FiniteOperationalErasureFailureAt C n → finiteOperationalErasureDistance C ≤ n := by sorry
