-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditLength_eq_card
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditLength_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:38:29.859901+00:00
-- url     : https://prove2.me/theorems/0a1d4a89-afba-44ed-b6d6-46a71263d526
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Length eq card
-- statement:
--   Physical coordinates are the actual complement, with no stored length witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L41-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L41-L45

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditLength_eq_card (i : ℕ) :
    f256QuditLength i = Fintype.card (f256SourceInput i).PivotComplement := by sorry
