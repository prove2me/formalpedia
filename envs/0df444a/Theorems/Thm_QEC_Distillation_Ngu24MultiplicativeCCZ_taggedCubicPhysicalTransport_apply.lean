-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_apply
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:32:12.625942+00:00
-- url     : https://prove2.me/theorems/607f03b7-5e9f-4667-b9c3-1780245a218a
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Physical Transport apply
-- statement:
--   The physical product has the total source phase on every amplitude.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L124-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L124-L139

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply (f : F →ₗ[ZMod 2] ZMod 2)
    (psi : TaggedThreeCopyRegister F J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhysicalTransport f psi label =
      taggedCubicPhaseAmplitude f Finset.univ label * psi label := by sorry
