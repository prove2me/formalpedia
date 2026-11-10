-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_sourceBinaryTaggedEncodingIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncodingIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:52:42.450174+00:00
-- url     : https://prove2.me/theorems/c0b3873d-984f-4629-ad5e-77a680320b28
-- title:
--   Ngu24 Binary: source Binary Tagged Encoding Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the source Binary Tagged Encoding Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L82-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L82-L93

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance 2000] QEC.Distillation.Ngu24Binary.binaryTaggedFinDecidableEq
variable {I Logical : Type} [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryTaggedLogicalDecidableEq

theorem QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncodingIsometry_basis (data : SourceInput F256 I Logical)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) Logical) :
    sourceBinaryTaggedEncodingIsometry data (registerBasisKet u) =
      taggedCosetNormalization data • ∑ h : ThreeCopyTag → data.H0,
        registerBasisKet (taggedPhysicalWordEmbedding data.PivotComplement
          (taggedShortenedCosetLabel data (logicalWordEmbedding (ThreeCopyTag × Logical) u) h)) := by sorry
