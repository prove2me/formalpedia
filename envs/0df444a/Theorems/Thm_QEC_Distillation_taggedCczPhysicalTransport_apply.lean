-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczPhysicalTransport_apply
-- name    : QEC.Distillation.taggedCczPhysicalTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:02:41.633294+00:00
-- url     : https://prove2.me/theorems/2c12dbb7-a17b-4063-93a4-de47c9205fc3
-- title:
--   Distillation: tagged Ccz Physical Transport apply
-- statement:
--   The physical product acts by the product of its concrete local phases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L83-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L83-L100

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

theorem QEC.Distillation.taggedCczPhysicalTransport_apply [Fintype ι] [DecidableEq ι]
    (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczPhysicalTransport psi label =
      (∏ site : ι, taggedCczAmplitude site label) * psi label := by sorry
