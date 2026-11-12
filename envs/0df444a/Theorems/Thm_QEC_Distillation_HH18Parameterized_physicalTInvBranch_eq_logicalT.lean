-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalTInvBranch_eq_logicalT
-- name    : QEC.Distillation.HH18Parameterized.physicalTInvBranch_eq_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:08.835681+00:00
-- url     : https://prove2.me/theorems/e11a1aac-ca16-4957-813a-d4ecc2ac27f1
-- title:
--   HH18 Parameterized: physical TInv Branch eq logical T
-- statement:
--   The parameterized physical target is exactly the encoded logical-`T` target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L109-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L109-L115

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.physicalTInvBranch_eq_logicalT {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    physicalTInvBranch h hdegree =
      (HH18PuncturedReedMuller.encodedCode h).encode
        (HH18PuncturedReedMuller.logicalT w m (logicalPlus m w)) := by sorry
