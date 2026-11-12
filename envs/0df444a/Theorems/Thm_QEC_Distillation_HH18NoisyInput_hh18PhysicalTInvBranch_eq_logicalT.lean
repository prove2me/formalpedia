-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18PhysicalTInvBranch_eq_logicalT
-- name    : QEC.Distillation.HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:32:20.389196+00:00
-- url     : https://prove2.me/theorems/600e397a-5345-49c0-851e-b67835695eb4
-- title:
--   HH18 Noisy Input: hh18 Physical TInv Branch eq logical T
-- statement:
--   The concrete error-free target branch is exactly the #759 encoded logical
--   `T` action; this is an equality derived from transversality, not a field of a
--   protocol specification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L371-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L371-L376

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

theorem QEC.Distillation.HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT :
    hh18PhysicalTInvBranch =
      hh18_15_1_0_encodedCode.encode
        (HH18PuncturedReedMuller.logicalT 0 4 hh18LogicalPlusInput) := by sorry
