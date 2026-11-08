-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_detectable_localOperator
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_detectable_localOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:18:51.447694+00:00
-- url     : https://prove2.me/theorems/e8f3f62e-8da3-4a14-a2fc-a5a98fbf4b42
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input detectable local Operator
-- statement:
--   Every actual tensor-local operator on fewer than `ceil(n/5)-K` qudits
--   is detectable on the concrete quantum code's full carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L95-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L95-L108

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_5d3c569749_91

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_detectable_localOperator (i : ℕ)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement => Fintype.card F256))
    (hS : S.selected.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (E : Operator S.selectedSystem) :
    DetectableOn (f256SourceInput i).quantumCode (FiniteAlphabet.localOperator S E) := by sorry
