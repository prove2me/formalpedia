-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedLogicalIsometry_intertwines_binaryLogicalCCZ
-- name    : QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_intertwines_binaryLogicalCCZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:52:04.412127+00:00
-- url     : https://prove2.me/theorems/46ca61c1-6d04-4214-a4a0-3e9e71992041
-- title:
--   Ngu24 Binary: tagged Logical Isometry intertwines binary Logical CCZ
-- statement:
--   RMFE logical restriction intertwines full operators, not only logical basis labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L70-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L70-L84

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

theorem QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_intertwines_binaryLogicalCCZ :
    (taggedCubicPhaseTransport (J := J) f256RMFEpsi Finset.univ).toLinearEquiv.toLinearMap.comp
        (taggedLogicalIsometry J).toLinearMap =
      (taggedLogicalIsometry J).toLinearMap.comp (binaryLogicalCCZ (J := J)).toLinearEquiv.toLinearMap := by sorry
