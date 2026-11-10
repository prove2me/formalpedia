-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_singleton
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:32:07.959159+00:00
-- url     : https://prove2.me/theorems/24123184-dd2a-41d6-be7c-076646af38ad
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Amplitude singleton
-- statement:
--   A single-site factor depends on exactly the three named coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L74-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L74-L79

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

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_singleton (f : F →ₗ[ZMod 2] ZMod 2) (site : J)
    (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseAmplitude f {site} label =
      PauliSymplectic.binaryPhaseScalar
        (f (label (.first, site) * label (.second, site) * label (.third, site))) := by sorry
