-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditEncodedCode_dimension
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:38:06.892443+00:00
-- url     : https://prove2.me/theorems/88f3b107-02f3-44d6-ae6b-bf6630f59067
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Encoded Code dimension
-- statement:
--   `K` is the number of logical qudits; the complex carrier dimension is `256^K`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L48-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L48-L56

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_dimension (i : ℕ) :
    (f256QuditEncodedCode i).code.dimension = 256 ^ f256MultiplicationLogicalCount i := by sorry
