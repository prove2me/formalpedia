-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18LogicalPlusInput_norm
-- name    : QEC.Distillation.HH18Protocol.hh18LogicalPlusInput_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:13.41326+00:00
-- url     : https://prove2.me/theorems/c223c99c-937e-4562-bcee-cc28f312c711
-- title:
--   HH18 Protocol: hh18 Logical Plus Input norm
-- statement:
--   The registered HH18 logical-plus input is normalized.  This public carrier
--   fact is shared by the physical branch and ideal-decoder layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalTypes.lean#L39-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalTypes.lean#L39-L49

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
universe u
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Protocol.hh18LogicalPlusInput_norm : ‖HH18NoisyInput.hh18LogicalPlusInput‖ = 1 := by sorry
