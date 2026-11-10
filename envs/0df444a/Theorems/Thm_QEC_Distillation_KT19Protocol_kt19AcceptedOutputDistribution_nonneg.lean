-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedOutputDistribution_nonneg
-- name    : QEC.Distillation.KT19Protocol.kt19AcceptedOutputDistribution_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:28:40.376979+00:00
-- url     : https://prove2.me/theorems/e8f8d45d-acff-4643-939b-a7f172d99573
-- title:
--   KT19 Protocol: kt19 Accepted Output Distribution nonneg
-- statement:
--   Every observed accepted-output label mass is nonnegative because it is a
--   Born weight of the actual finite magic-basis instrument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L2568-L2577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L2568-L2577

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

theorem QEC.Distillation.KT19Protocol.kt19AcceptedOutputDistribution_nonneg
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted)
    (label : PrimeQuditRegisterLabel q Logical) :
    0 ≤ kt19AcceptedOutputDistribution R mu hmu_nonneg hmu_sum hpos label := by sorry
