-- Prove2me | Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_acceptedDecodedWord_eq_routedMagic
-- name    : QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedDecodedWord_eq_routedMagic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:33:05.443211+00:00
-- url     : https://prove2.me/theorems/4c675b01-5d17-4751-947e-2fa1dad8c7d9
-- title:
--   KT19 Distillation Family: accepted Decoded Word eq routed Magic
-- statement:
--   Every physically accepted family word is decoded to the pure logical
--   magic-register word selected by the literal KT19 routing function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3267-L3281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean#L3267-L3281

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

theorem QEC.Distillation.KT19Protocol.KT19DistillationFamily.acceptedDecodedWord_eq_routedMagic
    (family : KT19DistillationFamily p l k)
    (error : Word (ZMod p) (KeptPunctureLocation p k))
    (haccepted : kt19AcceptedWord family.rowFamily error) :
    family.decoder
      (family.distillationInstrument.branchOperator .accepted
        (kt19WordInputDensity error).toOperator) =
      (DensityOperator.pureDensity
        (magicRegisterKet p (kt19Routing family error)) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num)).toOperator := by sorry
