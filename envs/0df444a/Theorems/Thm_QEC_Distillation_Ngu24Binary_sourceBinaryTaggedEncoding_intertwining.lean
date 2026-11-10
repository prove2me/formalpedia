-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_sourceBinaryTaggedEncoding_intertwining
-- name    : QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncoding_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:04:30.138356+00:00
-- url     : https://prove2.me/theorems/83fa3df3-5bfe-4489-a8ba-b8e530a7d1dd
-- title:
--   Ngu24 Binary: source Binary Tagged Encoding intertwining
-- statement:
--   The actual selected physical CCZ product implements all logical CCZs on every input state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L92-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L92-L113

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
variable {I Logical : Type} [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCubicLogicalDecidableEq

theorem QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncoding_intertwining (data : SourceInput F256 I Logical)
    (psi : TaggedThreeCopyRegister (ZMod 2) Logical) :
    binaryPhysicalCCZ (sourceBinaryTaggedEncodingIsometry data psi) =
      sourceBinaryTaggedEncodingIsometry data (binaryLogicalCCZ psi) := by sorry
