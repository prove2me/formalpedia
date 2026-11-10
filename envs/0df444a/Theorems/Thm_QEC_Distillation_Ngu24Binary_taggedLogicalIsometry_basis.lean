-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedLogicalIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:51:54.109246+00:00
-- url     : https://prove2.me/theorems/f5ca605e-6aee-404e-9548-b71987c0b57e
-- title:
--   Ngu24 Binary: tagged Logical Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the tagged Logical Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L51-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L51-L54

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

theorem QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_basis (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    taggedLogicalIsometry J (registerBasisKet u) =
      registerBasisKet (logicalWordEmbedding (ThreeCopyTag × J) u) := by sorry
