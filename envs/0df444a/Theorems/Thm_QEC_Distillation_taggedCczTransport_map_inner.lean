-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczTransport_map_inner
-- name    : QEC.Distillation.taggedCczTransport_map_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:00:05.434105+00:00
-- url     : https://prove2.me/theorems/6c41f5d3-04bb-4ca3-88d3-0eb9b5dd6214
-- title:
--   Distillation: tagged Ccz Transport map inner
-- statement:
--   Named inner-product preservation for the tagged single-coordinate transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L326-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L326-L330

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

theorem QEC.Distillation.taggedCczTransport_map_inner [Fintype ι] [DecidableEq ι]
    (site : ι) (psi chi : TaggedThreeCopyRegister F ι) :
    inner Complex (taggedCczTransport site psi) (taggedCczTransport site chi) =
      inner Complex psi chi := by sorry
