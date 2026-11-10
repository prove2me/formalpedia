-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedExponent_physicalWord
-- name    : QEC.Distillation.Ngu24Binary.binarySelectedExponent_physicalWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:54:08.736954+00:00
-- url     : https://prove2.me/theorems/a7ed95bd-1780-4ee9-bac4-271b489385b0
-- title:
--   Ngu24 Binary: binary Selected Exponent physical Word
-- statement:
--   The actual selected, inverse-permuted binary monomials reconstruct the weighted field cubic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L25-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L25-L36

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

theorem QEC.Distillation.Ngu24Binary.binarySelectedExponent_physicalWord
    (u : TaggedThreeCopyRegisterLabel F256 J) :
    binarySelectedExponent (taggedPhysicalWordEmbedding J u) =
      f256RMFEpsi (taggedCubicPhaseExponent Finset.univ u) := by sorry
