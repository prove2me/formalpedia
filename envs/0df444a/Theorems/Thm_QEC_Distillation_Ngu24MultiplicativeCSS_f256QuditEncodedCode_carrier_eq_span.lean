-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditEncodedCode_carrier_eq_span
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_carrier_eq_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:37:32.426368+00:00
-- url     : https://prove2.me/theorems/accfc2ba-937a-4b54-ad60-5766d9ff4e3c
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Encoded Code carrier eq span
-- statement:
--   These are precisely the source's uniform coset CSS states, extended by linearity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L59-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L59-L72

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_carrier_eq_span (i : ℕ) :
    (f256QuditEncodedCode i).code.carrier =
      Submodule.span Complex (Set.range (f256SourceInput i).shortenedCosetKet) := by sorry
