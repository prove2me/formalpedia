-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedRMFE_cubicExponent
-- name    : QEC.Distillation.Ngu24Binary.taggedRMFE_cubicExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:54:30.891207+00:00
-- url     : https://prove2.me/theorems/8b1f0227-757d-4315-8479-81ed12be0052
-- title:
--   Ngu24 Binary: tagged RMFE cubic Exponent
-- statement:
--   The Ngu24 Binary construction uses the tagged RMFE cubic Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L59-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L59-L67

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
omit [DecidableEq J]

theorem QEC.Distillation.Ngu24Binary.taggedRMFE_cubicExponent (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    f256RMFEpsi (taggedCubicPhaseExponent Finset.univ
      (logicalWordEmbedding (ThreeCopyTag × J) u)) =
      taggedCubicPhaseExponent Finset.univ u := by sorry
