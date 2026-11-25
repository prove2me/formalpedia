-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:02:15.368083+00:00
-- url     : https://prove2.me/theorems/b6014ae9-db30-5dad-be3e-6559fb259b49
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem sub 613bf1440878: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem sub 613bf1440878
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem sub 613bf1440878 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem sub 613bf1440878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L150-L162

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878 (M : SubFamily S x Ω) (I J : Chart x) {y : Ω}
    (hy : y ∈ M.sub (unionChart I J)) : ∃ D : ℕ, chartRatio I J ^ D * y ∈ M.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«exists_pow_mul_mem_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_sub_613bf1440878
