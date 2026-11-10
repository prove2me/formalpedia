-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_kt19DecoderChannel_rankOne_encoded
-- name    : QEC.Distillation.KT19Protocol.kt19DecoderChannel_rankOne_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:28:17.152215+00:00
-- url     : https://prove2.me/theorems/7f5d9595-181c-4c57-a181-2b9f967edb93
-- title:
--   KT19 Protocol: kt19 Decoder Channel rank One encoded
-- statement:
--   On the coherent encoded carrier, the total decoder agrees with the actual
--   inverse-decoding branch; all complement Kraus terms vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L1408-L1436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L1408-L1436

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

theorem QEC.Distillation.KT19Protocol.kt19DecoderChannel_rankOne_encoded
    (R : CubicRowFamily q Logical Stabilizer Site)
    (psi : PrimeQuditRegister q Logical) :
    kt19DecoderChannel R (InnerProductSpace.rankOne Complex
      (kt19DecoderEncodingIsometry R psi)
      (kt19DecoderEncodingIsometry R psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry
