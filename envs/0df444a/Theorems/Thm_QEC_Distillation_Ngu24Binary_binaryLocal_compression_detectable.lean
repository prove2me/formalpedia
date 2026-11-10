-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLocal_compression_detectable
-- name    : QEC.Distillation.Ngu24Binary.binaryLocal_compression_detectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:42:36.229144+00:00
-- url     : https://prove2.me/theorems/bc6576e2-5617-4954-a157-fb5276f12ad9
-- title:
--   Ngu24 Binary: binary Local compression detectable
-- statement:
--   Arbitrary actual binary-local operators pull back to detectable native operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L44-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L44-L76

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

theorem QEC.Distillation.Ngu24Binary.binaryLocal_compression_detectable (i : Nat)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2))
    (hS : S.selected.card < f256QuditDistanceBound i) (E : Operator S.selectedSystem) :
    DetectableOn (f256SourceInput i).quantumCode
      (ComputationalEmbedding.compress
        ⟨physicalWordEmbedding (f256SourceInput i).PivotComplement,
          physicalWordEmbedding_injective (f256SourceInput i).PivotComplement⟩
        (S.extendLocalToRegister E)) := by sorry
