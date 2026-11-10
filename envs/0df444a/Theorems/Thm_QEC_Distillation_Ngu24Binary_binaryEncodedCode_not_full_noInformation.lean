-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_not_full_noInformation
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_not_full_noInformation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:45:31.812001+00:00
-- url     : https://prove2.me/theorems/748d5abd-7aef-4d63-813f-cb2dc5c0521d
-- title:
--   Ngu24 Binary: binary Encoded Code not full no Information
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code not full no Information property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L35-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L35-L60

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_6d70a6dbef_22

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_not_full_noInformation (i : Nat) :
    ¬ QuditSubsystem.NoInformationOn (binaryEncodedCode i).code
      (QuditSubsystem.fullRegion (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2)) := by sorry
