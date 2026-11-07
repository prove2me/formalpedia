-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczPhysicalTransport_apply_basis
-- name    : QEC.Distillation.taggedCczPhysicalTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:02:34.691493+00:00
-- url     : https://prove2.me/theorems/36c1a640-cb87-4ad9-8c72-d63de35dd307
-- title:
--   Distillation: tagged Ccz Physical Transport apply basis
-- statement:
--   The physical product has the coordinatewise phase action on every tagged basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L103-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L103-L114

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

theorem QEC.Distillation.taggedCczPhysicalTransport_apply_basis [Fintype ι] [DecidableEq ι]
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczPhysicalTransport
        (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label) =
      (∏ site : ι, taggedCczAmplitude site label) •
        EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label := by sorry
