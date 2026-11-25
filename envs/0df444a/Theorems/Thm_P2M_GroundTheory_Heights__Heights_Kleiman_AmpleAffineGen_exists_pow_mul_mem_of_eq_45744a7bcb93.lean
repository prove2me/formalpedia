-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:34.218028+00:00
-- url     : https://prove2.me/theorems/c0116051-9efb-4a92-8017-1d1fa0fa74c4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem of eq 45744a7bcb93: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem of eq 45744a7bcb93
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem of eq 45744a7bcb93 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen exists pow mul mem of eq 45744a7bcb93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L164-L168

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93 (L : LineBundle S x) {F : SubSystem S x Ω}
    (hL : L.toSubSystem = F) (I J : Chart x) {y : Ω} (hy : y ∈ F.sub (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * y ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«exists_pow_mul_mem_of_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
