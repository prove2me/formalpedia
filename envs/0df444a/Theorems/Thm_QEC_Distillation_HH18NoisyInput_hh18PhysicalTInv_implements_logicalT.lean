-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18PhysicalTInv_implements_logicalT
-- name    : QEC.Distillation.HH18NoisyInput.hh18PhysicalTInv_implements_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:52:46.746226+00:00
-- url     : https://prove2.me/theorems/89db112d-adb7-4199-9ab9-98a45d38e118
-- title:
--   HH18 Noisy Input: hh18 Physical TInv implements logical T
-- statement:
--   The orientation supplied by #759 for the actual 15-site encoding:
--   physical `T†` implements logical `T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L354-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L354-L360

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18NoisyInput.hh18PhysicalTInv_implements_logicalT :
    hh18_15_1_0_encodedCode.ImplementsLogicalGate
      (HH18PuncturedReedMuller.physicalTInv 0 4)
      (HH18PuncturedReedMuller.logicalT 0 4) := by sorry
