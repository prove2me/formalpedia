-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_apply_coset
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:32:17.792828+00:00
-- url     : https://prove2.me/theorems/dae94a8e-af20-4196-b6e2-943b68d5f1c5
-- title:
--   Ngu24 Multiplicative CCZ: tagged Cubic Physical Transport apply coset
-- statement:
--   Every summand of the actual normalized coset encoder has the same logical phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L192-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CubicPhase.lean#L192-L199

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

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply_coset (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedCubicPhysicalTransport f (taggedShortenedCosetKet data label) =
      taggedCubicPhaseAmplitude f Finset.univ label • taggedShortenedCosetKet data label := by sorry
