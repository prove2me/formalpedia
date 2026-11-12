-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalTInv_implements_logicalT
-- name    : QEC.Distillation.HH18Parameterized.physicalTInv_implements_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:33.698206+00:00
-- url     : https://prove2.me/theorems/ee95f9c9-e973-4ff1-bf7e-7dbc22231fb4
-- title:
--   HH18 Parameterized: physical TInv implements logical T
-- statement:
--   The actual transversal inverse-`T` transport implements logical `T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L96-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L96-L101

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalTInv_implements_logicalT

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.physicalTInv_implements_logicalT {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (HH18PuncturedReedMuller.encodedCode h).ImplementsLogicalGate
      (HH18PuncturedReedMuller.physicalTInv w m)
      (HH18PuncturedReedMuller.logicalT w m) := by sorry
