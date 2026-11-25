-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:12:17.702134+00:00
-- url     : https://prove2.me/theorems/d0e27ba7-efd1-41e9-8371-d3c5de7c8ae3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem 866e61ad51fa: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem 866e61ad51fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem 866e61ad51fa construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem 866e61ad51fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L64-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L64-L148

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa (I J : Chart x) {c : Ω} (hc : c ∈ chartRing S x (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * c ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«exists_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
