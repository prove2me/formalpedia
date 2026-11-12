-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthStageResource_eq_noisyResources
-- name    : QEC.Distillation.HH18Protocol.hh18DepthStageResource_eq_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:29:42.091207+00:00
-- url     : https://prove2.me/theorems/fc5dbf77-03eb-4d04-9039-cb6c9b22df12
-- title:
--   HH18 Protocol: hh18 Depth Stage Resource eq noisy Resources
-- statement:
--   The HH18 Protocol construction uses the hh18 Depth Stage Resource eq noisy Resources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L766-L771
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L766-L771

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

theorem QEC.Distillation.HH18Protocol.hh18DepthStageResource_eq_noisyResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall depth =
      noisyResources (hh18ErrorIteration epsilon hsmall depth) := by sorry
