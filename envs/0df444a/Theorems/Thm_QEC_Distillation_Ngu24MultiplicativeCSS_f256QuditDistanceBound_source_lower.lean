-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditDistanceBound_source_lower
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditDistanceBound_source_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:39:23.444493+00:00
-- url     : https://prove2.me/theorems/2d125a36-b63b-44e1-aeae-814910ceec97
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Distance Bound source lower
-- statement:
--   The source's rational distance estimate follows from the actual integer bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L89-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L89-L99

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditDistanceBound_source_lower (i : ℕ) :
    (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤
      f256QuditDistanceBound i := by sorry
