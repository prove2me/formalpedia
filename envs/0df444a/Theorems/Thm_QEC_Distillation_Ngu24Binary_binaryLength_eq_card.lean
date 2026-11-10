-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLength_eq_card
-- name    : QEC.Distillation.Ngu24Binary.binaryLength_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:44:30.110784+00:00
-- url     : https://prove2.me/theorems/24ed69f2-f5bc-4bd2-b50b-9b237d1b92ec
-- title:
--   Ngu24 Binary: binary Length eq card
-- statement:
--   The Ngu24 Binary construction uses the binary Length eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean#L30-L33

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

theorem QEC.Distillation.Ngu24Binary.binaryLength_eq_card (i : Nat) :
    binaryLength i = Fintype.card ((f256SourceInput i).PivotComplement × Fin 512) := by sorry
