-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseAmplitude_coset
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:31:58.524038+00:00
-- url     : https://prove2.me/theorems/2fed26da-0cc7-4bf2-be39-ae31687ea2cd
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Phase Amplitude coset
-- statement:
--   Apply the chosen functional to the already-proved field-valued cubic identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L182-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L182-L189

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
variable [Fintype I] [Fintype Logical] [CharP F 2]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_bfada1b37a_179

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_coset (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    taggedCubicPhaseAmplitude f Finset.univ (taggedShortenedCosetLabel data label h) =
      taggedCubicPhaseAmplitude f Finset.univ label := by sorry
