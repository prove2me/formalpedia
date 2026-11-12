-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_decodedCorrectableAcceptedOutput_eq_logicalT
-- name    : QEC.Distillation.HH18SyndromeDecoding.decodedCorrectableAcceptedOutput_eq_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:49:19.838357+00:00
-- url     : https://prove2.me/theorems/d15eb999-f569-42b3-8747-aee192ad402c
-- title:
--   HH18 Syndrome Decoding: decoded Correctable Accepted Output eq logical T
-- statement:
--   The correctable zero-syndrome route decodes to the established logical-T output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L514-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L514-L530

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18SyndromeDecoding.decodedCorrectableAcceptedOutput_eq_logicalT
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) :
    decodedCorrectableAcceptedOutput error hweight haccept =
      HH18PuncturedReedMuller.logicalT 0 4
        HH18NoisyInput.hh18LogicalPlusInput := by sorry
