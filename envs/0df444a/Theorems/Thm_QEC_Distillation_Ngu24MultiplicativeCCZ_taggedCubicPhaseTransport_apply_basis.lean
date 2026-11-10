-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply_basis
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:32:19.840135+00:00
-- url     : https://prove2.me/theorems/ab7b546f-628d-4c59-8d9b-9456c461716c
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Transport apply basis
-- statement:
--   The Ngu24 Multiplicative CCZ construction uses the tagged Cubic Phase Transport apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L60-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L60-L70

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

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply_basis (f : F →ₗ[ZMod 2] ZMod 2)
    (sites : Finset J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseTransport f sites (registerBasisKet label) =
      taggedCubicPhaseAmplitude f sites label • registerBasisKet label := by sorry
