-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczTransport_commute
-- name    : QEC.Distillation.taggedCczTransport_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:12:07.130586+00:00
-- url     : https://prove2.me/theorems/654f7646-623b-42aa-9436-faf143f99ab9
-- title:
--   Distillation: tagged Ccz Transport commute
-- statement:
--   Tagged local CCZ transports commute because both are concrete diagonal maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L54-L60

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

theorem QEC.Distillation.taggedCczTransport_commute [Fintype ι] [DecidableEq ι]
    (first second : ι) (psi : TaggedThreeCopyRegister F ι) :
    taggedCczTransport first (taggedCczTransport second psi) =
      taggedCczTransport second (taggedCczTransport first psi) := by sorry
