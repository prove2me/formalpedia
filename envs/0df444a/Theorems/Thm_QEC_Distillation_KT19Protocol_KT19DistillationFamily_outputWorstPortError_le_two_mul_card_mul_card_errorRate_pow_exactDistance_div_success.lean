-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_exactDistance_div_success
-- name    : QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_exactDistance_div_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:31:10.74021+00:00
-- url     : https://prove2.me/theorems/561aab90-aee9-4033-b248-6b50720d6f34
-- title:
--   KT19 Distillation Family: output Worst Port Error le two mul card mul card error Rate pow exact Distance div success
-- statement:
--   The actual family output error obeys a success-adjusted exact-distance
--   IID recurrence, derived from its physical measurement, decoder, readout, and
--   finite accepted-word support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L5073-L5096
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L5073-L5096

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
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]

theorem QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_exactDistance_div_success
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (heps : kt19ErrorRate mu < 1) :
    outputWorstPortError family mu hmu_nonneg hmu_sum ≤
      2 * (Fintype.card (PrimeQuditRegisterLabel p (Fin k)) : ℝ) *
        (((Fintype.card (Word (ZMod p) (KeptPunctureLocation p k)) : ℝ) *
          kt19ErrorRate mu ^ (l + 1 - k)) /
          kt19Success family.rowFamily mu hmu_nonneg hmu_sum) := by sorry
