-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:04:09.876537+00:00
-- url     : https://prove2.me/theorems/cda9e1b0-3592-4fa4-ba1a-437bf0a57832
-- title:
--   HH18 Parameterized: decoded Retry Pool Dyadic Output Slots card
-- statement:
--   The selected output carrier has exactly one logical-site slot for every
--   requested accepted block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L146-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean#L146-L148

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicOutputSlots_card (required m w : Nat) :
    Fintype.card (Fin required × LogicalSite m w) = required * logicalOutputCount m w := by sorry
