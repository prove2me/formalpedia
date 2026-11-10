-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditEncodedCode_measurementDistance
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:39:31.463801+00:00
-- url     : https://prove2.me/theorems/d6b9ad1b-d419-4a9f-bf0b-7e06328b079c
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Encoded Code measurement Distance
-- statement:
--   The parameter bound is realized by standard semantic measurement distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L102-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L102-L107

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_measurementDistance (i : ℕ) :
    QuditSubsystem.BPTMeasurementDistance
      ((f256QuditEncodedCode i).code.transport
        (FiniteAlphabet.registerUnitary F256 (f256SourceInput i).PivotComplement))
      (f256QuditDistanceBound i) := by sorry
