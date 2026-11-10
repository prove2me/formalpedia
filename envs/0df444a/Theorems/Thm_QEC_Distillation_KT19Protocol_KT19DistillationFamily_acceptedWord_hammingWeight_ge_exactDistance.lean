-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_acceptedWord_hammingWeight_ge_exactDistance
-- name    : QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedWord_hammingWeight_ge_exactDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:31:08.141818+00:00
-- url     : https://prove2.me/theorems/e4de2ffa-7ef9-4fb4-bed6-fcc546bfbf33
-- title:
--   KT19 Distillation Family: accepted Word hamming Weight ge exact Distance
-- statement:
--   A nonzero physically accepted word has the exact family distance lower
--   bound, obtained from the constructed stabilizer code rather than a stored
--   error-tail conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3530-L3540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3530-L3540

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
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]

theorem QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedWord_hammingWeight_ge_exactDistance
    (family : KT19DistillationFamily p l k)
    (error : Word (ZMod p) (KeptPunctureLocation p k))
    (haccepted : kt19AcceptedWord family.rowFamily error) (herror : error ≠ 0) :
    l + 1 - k ≤ HammingWeight error := by sorry
