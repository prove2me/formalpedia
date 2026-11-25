-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:01.585033+00:00
-- url     : https://prove2.me/theorems/08cd3c5b-3fb6-4829-b7b8-bff90d7b10b0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm sub pow a678e760a862: P2 M Ground Theory Heights  Heights Kleiman KThm sub pow a678e760a862
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm sub pow a678e760a862 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm sub pow a678e760a862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L29-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862 (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«sub_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
