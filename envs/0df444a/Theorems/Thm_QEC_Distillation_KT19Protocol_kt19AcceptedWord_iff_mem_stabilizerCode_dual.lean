-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedWord_iff_mem_stabilizerCode_dual
-- name    : QEC.Distillation.KT19Protocol.kt19AcceptedWord_iff_mem_stabilizerCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:28:48.006867+00:00
-- url     : https://prove2.me/theorems/6de26dd4-6756-4539-9a8f-2e1a1f718b18
-- title:
--   KT19 Protocol: kt19 Accepted Word iff mem stabilizer Code dual
-- statement:
--   Trivial stabilizer syndrome is exactly membership in the dual of the
--   actual stabilizer-row code.  The result is derived by span induction, so no
--   accepted-word support is supplied as protocol data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L327-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L327-L353

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

theorem QEC.Distillation.KT19Protocol.kt19AcceptedWord_iff_mem_stabilizerCode_dual
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) :
    kt19AcceptedWord R word ↔ word ∈ (kt19StabilizerCode R).dual.carrier := by sorry
