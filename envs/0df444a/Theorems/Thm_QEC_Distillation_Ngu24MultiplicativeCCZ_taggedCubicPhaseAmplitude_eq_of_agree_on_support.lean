-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_eq_of_agree_on_support
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_eq_of_agree_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:32:50.503527+00:00
-- url     : https://prove2.me/theorems/463dbc5b-378b-41ab-b62c-622c525e8489
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Amplitude eq of agree on support
-- statement:
--   The local gate's amplitude is unchanged when its declared triple is unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L82-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L82-L90

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

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_eq_of_agree_on_support
    (f : F →ₗ[ZMod 2] ZMod 2) (site : J)
    (x y : TaggedThreeCopyRegisterLabel F J)
    (h : ∀ coordinate ∈ coordinateSupport site, x coordinate = y coordinate) :
    taggedCubicPhaseAmplitude f {site} x = taggedCubicPhaseAmplitude f {site} y := by sorry
