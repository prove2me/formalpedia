-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256QuditFamily_cubic_implements_logical
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditFamily_cubic_implements_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:39:39.50096+00:00
-- url     : https://prove2.me/theorems/75ec5958-5c5e-430d-ae47-c557f0b24574
-- title:
--   Ngu24 Multiplicative CSS: f256 Qudit Family cubic implements logical
-- statement:
--   Every binary-linear cubic phase is implemented on all logical coordinates
--   through the actual full three-tag encoding equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L117-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean#L117-L122

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
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_111
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_112

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditFamily_cubic_implements_logical (i : ℕ)
    (f : F256 →ₗ[ZMod 2] ZMod 2) :
    (taggedEncodedCode (f256SourceInput i)).ImplementsLogicalGate
      (taggedCubicPhysicalTransport f)
      (taggedCubicPhaseTransport f Finset.univ) := by sorry
