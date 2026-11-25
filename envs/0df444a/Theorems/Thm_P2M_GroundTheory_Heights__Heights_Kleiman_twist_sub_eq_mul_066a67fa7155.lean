-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_mul_066a67fa7155
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_mul_066a67fa7155
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:05.266906+00:00
-- url     : https://prove2.me/theorems/1e4da21a-40ec-5db9-b54d-b6f30d6e1f18
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist sub eq mul 066a67fa7155: P2 M Ground Theory Heights  Heights Kleiman twist sub eq mul 066a67fa7155
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist sub eq mul 066a67fa7155 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist sub eq mul 066a67fa7155 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_mul_066a67fa7155 (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_sub_eq_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_mul_066a67fa7155
