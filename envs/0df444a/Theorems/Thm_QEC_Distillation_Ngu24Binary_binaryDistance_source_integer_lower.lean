-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_source_integer_lower
-- name    : QEC.Distillation.Ngu24Binary.binaryDistance_source_integer_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:47:09.970202+00:00
-- url     : https://prove2.me/theorems/a5763c3e-74b9-4559-bffc-7b845169e294
-- title:
--   Ngu24 Binary: binary Distance source integer lower
-- statement:
--   The Ngu24 Binary construction uses the binary Distance source integer lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L71-L74

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

theorem QEC.Distillation.Ngu24Binary.binaryDistance_source_integer_lower (i : Nat) :
    f256QuditDistanceBound i ≤ binaryDistance i := by sorry
