-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_hasLogicalEndpoint_iff_not_detectableOn
-- name    : QEC.Coding.PauliErrorPath.hasLogicalEndpoint_iff_not_detectableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:52:49.953378+00:00
-- url     : https://prove2.me/theorems/a264edf5-aa6d-4018-9e16-9e55ba20d560
-- title:
--   Pauli Error Path: has Logical Endpoint iff not detectable On
-- statement:
--   The path predicate is exactly the existing M3 nondetectability sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L207-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L207-L213

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath

theorem QEC.Coding.PauliErrorPath.hasLogicalEndpoint_iff_not_detectableOn
    (γ : PauliErrorPath (ι := ι)) (Q : StabilizerCode.SourceValidBinary ι) :
    γ.HasLogicalEndpoint Q ↔
      ¬ Semantics.DetectableOn Q.1.code (toQubitOperator γ.endpoint) := by sorry
