-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_codeDistance_eq_binomialTail
-- name    : QEC.Distillation.HH18Parameterized.codeDistance_eq_binomialTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:07.805022+00:00
-- url     : https://prove2.me/theorems/eb2879ee-814c-46df-b776-42271042f562
-- title:
--   HH18 Parameterized: code Distance eq binomial Tail
-- statement:
--   The named distance is the exact punctured Reed--Muller distance formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L63-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L63-L65

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

theorem QEC.Distillation.HH18Parameterized.codeDistance_eq_binomialTail (r w : Nat) :
    codeDistance r w = binomialTail (r + 1) w := by sorry
