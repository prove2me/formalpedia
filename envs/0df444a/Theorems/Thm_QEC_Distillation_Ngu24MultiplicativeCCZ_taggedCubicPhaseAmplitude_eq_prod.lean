-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_eq_prod
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:31:50.755162+00:00
-- url     : https://prove2.me/theorems/77515264-2d5a-4c0a-b3e5-ddef14561b99
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Amplitude eq prod
-- statement:
--   Binary linearity converts the total phase into the physical local product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L94-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L94-L99

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
omit [Fintype F] [Fintype J] [DecidableEq J]

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_eq_prod (f : F →ₗ[ZMod 2] ZMod 2)
    (sites : Finset J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseAmplitude f sites label =
      ∏ site ∈ sites, taggedCubicPhaseAmplitude f {site} label := by sorry
