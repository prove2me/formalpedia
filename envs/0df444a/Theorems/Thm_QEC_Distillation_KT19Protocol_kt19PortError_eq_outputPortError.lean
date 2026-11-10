-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_kt19PortError_eq_outputPortError
-- name    : QEC.Distillation.KT19Protocol.kt19PortError_eq_outputPortError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:32:30.917603+00:00
-- url     : https://prove2.me/theorems/734e608b-1b71-4349-b3bb-ddbbe0a22ca2
-- title:
--   KT19 Protocol: kt19 Port Error eq output Port Error
-- statement:
--   The accepted conditional port error is the generic operational port
--   error evaluated at the actual decoded positive-mass accepted density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L2621-L2631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L2621-L2631

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]

theorem QEC.Distillation.KT19Protocol.kt19PortError_eq_outputPortError
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted)
    (port : Logical) :
    kt19PortError R mu hmu_nonneg hmu_sum hpos port =
      kt19OutputPortError
        ((kt19DecoderChannel R).mapDensity
          (kt19EndpointConditional R mu hmu_nonneg hmu_sum .accepted hpos)) port := by sorry
