-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:51.368707+00:00
-- url     : https://prove2.me/theorems/c031f932-eff9-41a1-bdfb-65b43d301907
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart left 2c27ecd7d652: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart left 2c27ecd7d652
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart left 2c27ecd7d652 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart left 2c27ecd7d652 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L22-L23

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652 (I J : Chart x) : I.1 ⊆ (unionChart I J).1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«subset_unionChart_left» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652
