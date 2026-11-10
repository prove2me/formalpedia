-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_intertwines_physicalIsometry
-- name    : QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_intertwines_physicalIsometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:56:50.430401+00:00
-- url     : https://prove2.me/theorems/4f66a203-21d0-4803-9c07-fe200cfd88a1
-- title:
--   Ngu24 Binary: binary Physical CCZ intertwines physical Isometry
-- statement:
--   MFE transversality is an equality on the whole field-labelled Hilbert space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L39-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCubicBridge.lean#L39-L51

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

theorem QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_intertwines_physicalIsometry :
    (binaryPhysicalCCZ (J := J)).toLinearEquiv.toLinearMap.comp
        (taggedPhysicalIsometry J).toLinearMap =
      (taggedPhysicalIsometry J).toLinearMap.comp
        (taggedCubicPhysicalTransport (J := J) f256RMFEpsi).toLinearEquiv.toLinearMap := by sorry
