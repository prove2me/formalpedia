-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:31:58.864006+00:00
-- url     : https://prove2.me/theorems/6bff37e8-6730-4582-87ea-5fa9eca14e0d
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Transport apply
-- statement:
--   The Ngu24 Multiplicative CCZ construction uses the tagged Cubic Phase Transport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L55-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L55-L58

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

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J)
    (psi : TaggedThreeCopyRegister F J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseTransport f sites psi label =
      taggedCubicPhaseAmplitude f sites label * psi label := by sorry

attribute [defeq] QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
