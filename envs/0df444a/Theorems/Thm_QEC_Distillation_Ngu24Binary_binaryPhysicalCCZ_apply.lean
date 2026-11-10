-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:41:50.286763+00:00
-- url     : https://prove2.me/theorems/6ac25104-0108-462d-ad33-df99d3e5d785
-- title:
--   Ngu24 Binary: binary Physical CCZ apply
-- statement:
--   The Ngu24 Binary construction uses the binary Physical CCZ apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L98-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L98-L117

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]

theorem QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ psi label =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) * psi label := by sorry
