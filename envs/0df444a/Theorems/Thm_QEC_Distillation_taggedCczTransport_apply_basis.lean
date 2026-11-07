-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczTransport_apply_basis
-- name    : QEC.Distillation.taggedCczTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:00:23.373126+00:00
-- url     : https://prove2.me/theorems/2168c86f-7883-4fc3-bffe-8b2794caba1e
-- title:
--   Distillation: tagged Ccz Transport apply basis
-- statement:
--   The tagged lift acts by the local CCZ phase on each tagged basis ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L333-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L333-L343

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

theorem QEC.Distillation.taggedCczTransport_apply_basis [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczTransport site (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label) =
      taggedCczAmplitude site label •
        EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label := by sorry
