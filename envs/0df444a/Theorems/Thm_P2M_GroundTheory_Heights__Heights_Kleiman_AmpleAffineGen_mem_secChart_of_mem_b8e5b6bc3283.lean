-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_secChart_of_mem_b8e5b6bc3283
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_secChart_of_mem_b8e5b6bc3283
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:14.671859+00:00
-- url     : https://prove2.me/theorems/cafd0de2-73dd-44d1-8333-96cbbde5c41d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem sec Chart of mem b8e5b6bc3283: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem sec Chart of mem b8e5b6bc3283
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem sec Chart of mem b8e5b6bc3283 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem sec Chart of mem b8e5b6bc3283 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L250-L252

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_secChart_of_mem_b8e5b6bc3283 {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ (Q.twist (H.pow b)).sub I) : z ∈ secChart Q H m b h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«mem_secChart_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_secChart_of_mem_b8e5b6bc3283
