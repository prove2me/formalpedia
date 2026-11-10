-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleAmplitude_eq_of_agree_on_support
-- name    : QEC.Distillation.Ngu24Binary.binaryTripleAmplitude_eq_of_agree_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:59:14.242463+00:00
-- url     : https://prove2.me/theorems/3869e68a-effd-44b0-96ac-6385ee3fd256
-- title:
--   Ngu24 Binary: binary Triple Amplitude eq of agree on support
-- statement:
--   The local phase depends only on the three coordinates in its declared support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L58-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L58-L65

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J]

theorem QEC.Distillation.Ngu24Binary.binaryTripleAmplitude_eq_of_agree_on_support (x : J × Fin 512)
    (a b : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512))
    (h : ∀ v ∈ binaryTripleSupport J x, a v = b v) :
    binaryTripleAmplitude x a = binaryTripleAmplitude x b := by sorry
