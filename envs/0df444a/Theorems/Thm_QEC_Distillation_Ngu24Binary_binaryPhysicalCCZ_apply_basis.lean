-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_apply_basis
-- name    : QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:50:35.835626+00:00
-- url     : https://prove2.me/theorems/8c3f3023-0393-430e-a007-f2da863d284b
-- title:
--   Ngu24 Binary: binary Physical CCZ apply basis
-- statement:
--   The Ngu24 Binary construction uses the binary Physical CCZ apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L119-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean#L119-L127

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]

theorem QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply_basis
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ (registerBasisKet label) =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) • registerBasisKet label := by sorry
