-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18AcceptedOutputAsNextInput_eq_noisyTInvResource
-- name    : QEC.Distillation.HH18Protocol.hh18AcceptedOutputAsNextInput_eq_noisyTInvResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:30:53.614298+00:00
-- url     : https://prove2.me/theorems/89d1043c-ae70-42f8-abcb-3612863dba1f
-- title:
--   HH18 Protocol: hh18 Accepted Output As Next Input eq noisy TInv Resource
-- statement:
--   The literal physical next input is the existing noisy `T†` resource at
--   the reached raw Born error rate, under its derived cubic smallness proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L173-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L173-L183

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.hh18AcceptedOutputAsNextInput_eq_noisyTInvResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) :
    hh18AcceptedOutputAsNextInput epsilon =
      HH18NoisyInput.noisyTInvResource (hh18NextInputErrorRate epsilon hsmall) := by sorry
