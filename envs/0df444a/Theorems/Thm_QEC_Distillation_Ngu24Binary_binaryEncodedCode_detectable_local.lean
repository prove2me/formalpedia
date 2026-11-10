-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_detectable_local
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_detectable_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:42:39.833179+00:00
-- url     : https://prove2.me/theorems/efa197a2-f745-492e-80bf-4ac8421c98c9
-- title:
--   Ngu24 Binary: binary Encoded Code detectable local
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code detectable local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L78-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L78-L95

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_9a39a2a69e_41

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_detectable_local (i : Nat)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2))
    (hS : S.selected.card < f256QuditDistanceBound i) (E : Operator S.selectedSystem) :
    DetectableOn (binaryEncodedCode i).code (S.extendLocalToRegister E) := by sorry
