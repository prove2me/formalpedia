-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputWorstPortError_le_smallErrorRecurrence
-- name    : QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputWorstPortError_le_smallErrorRecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:34:19.68844+00:00
-- url     : https://prove2.me/theorems/7f465df1-10b3-4b4d-be7b-bb40e753e0e4
-- title:
--   KT19 Distillation Family: output Worst Port Error le small Error Recurrence
-- statement:
--   On the explicit domain `(p-k) ε ≤ 1/2`, the actual physical output error
--   obeys the denominator-free recurrence required for iteration:
--   `ε_out ≤ C(p,l,k) ε^(l+1-k)`.  The success lower bound is derived from the
--   literal all-zero IID word and Bernoulli's inequality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L5110-L5182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L5110-L5182

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

theorem QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputWorstPortError_le_smallErrorRecurrence
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate mu ≤ 1 / 2) :
    outputWorstPortError family mu hmu_nonneg hmu_sum ≤
      smallErrorRecurrenceConstant family *
        kt19ErrorRate mu ^ (l + 1 - k) := by sorry
