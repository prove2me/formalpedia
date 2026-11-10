-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedPhysicalIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.taggedPhysicalIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:49:44.449048+00:00
-- url     : https://prove2.me/theorems/3ea2d9cd-0c0d-47ad-bd1a-474b80e0b11e
-- title:
--   Ngu24 Binary: tagged Physical Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the tagged Physical Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L56-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L56-L59

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

theorem QEC.Distillation.Ngu24Binary.taggedPhysicalIsometry_basis (u : TaggedThreeCopyRegisterLabel F256 J) :
    taggedPhysicalIsometry J (registerBasisKet u) =
      registerBasisKet (taggedPhysicalWordEmbedding J u) := by sorry
