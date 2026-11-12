-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_next_le_quarter
-- name    : QEC.Distillation.HH18Protocol.iteration_next_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:32:04.209971+00:00
-- url     : https://prove2.me/theorems/a0e82a43-3ae0-4fd6-82b4-5211577dd886
-- title:
--   HH18 Protocol: iteration next le quarter
-- statement:
--   The actual next reached rate contracts by a factor of four.  The
--   successor is exposed only by definitional reduction; its smallness proof is
--   proof-irrelevant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L487-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L487-L531

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

theorem QEC.Distillation.HH18Protocol.iteration_next_le_quarter (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ErrorIteration epsilon hsmall (depth + 1)).1 ≤
      (hh18ErrorIteration epsilon hsmall depth).1 / 4 := by sorry
