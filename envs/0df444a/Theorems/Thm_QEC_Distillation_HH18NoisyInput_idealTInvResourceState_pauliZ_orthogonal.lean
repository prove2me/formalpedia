-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_idealTInvResourceState_pauliZ_orthogonal
-- name    : QEC.Distillation.HH18NoisyInput.idealTInvResourceState_pauliZ_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:31:05.221689+00:00
-- url     : https://prove2.me/theorems/b8b1389e-2e80-44be-ad9c-505c79b89985
-- title:
--   HH18 Noisy Input: ideal TInv Resource State pauli Z orthogonal
-- statement:
--   The `Z`-flipped equatorial resource is exactly orthogonal to the ideal one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L78-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L78-L95

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

theorem QEC.Distillation.HH18NoisyInput.idealTInvResourceState_pauliZ_orthogonal :
    inner Complex idealTInvResourceState (pauliZ idealTInvResourceState) = 0 := by sorry
