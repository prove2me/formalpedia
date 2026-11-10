-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
-- name    : QEC.Distillation.KT19Protocol.p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:30:27.401899+00:00
-- url     : https://prove2.me/theorems/dc3ba009-2d78-4e54-b1cc-5e8ef0d67713
-- title:
--   KT19 Protocol: p11 Accepted Residual Error le card error Rate pow three div success
-- statement:
--   Distance three bounds the normalized p=11 accepted-error tail by the
--   actual physical success mass.  No success-free recurrence is inferred here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3973-L3985
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3973-L3985

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
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime
attribute [local instance] QEC.Distillation.KT19Protocol.p11NeZero
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero

theorem QEC.Distillation.KT19Protocol.p11AcceptedResidualError_le_card_errorRate_pow_three_div_success
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    p11AcceptedResidualError mu hmu_nonneg hmu_sum ≤
      ((Fintype.card (Word (ZMod 11) (KeptPunctureLocation 11 2)) : ℝ) *
        kt19ErrorRate mu ^ 3) /
        kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum := by sorry
