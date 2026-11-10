-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedEncodingIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:01:16.467887+00:00
-- url     : https://prove2.me/theorems/c089be74-6bbc-443f-a202-a479d373506f
-- title:
--   Ngu24 Binary: binary Tagged Encoding Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the binary Tagged Encoding Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L125-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L125-L133

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

theorem QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_basis (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i (registerBasisKet u) =
      taggedCosetNormalization (f256SourceInput i) •
        ∑ h : ThreeCopyTag → (f256SourceInput i).H0,
          registerBasisKet (binaryTaggedCosetLabel i u h) := by sorry
