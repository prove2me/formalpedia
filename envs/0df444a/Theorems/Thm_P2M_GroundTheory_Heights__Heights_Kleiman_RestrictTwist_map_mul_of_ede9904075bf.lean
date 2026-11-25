-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:24.550804+00:00
-- url     : https://prove2.me/theorems/82868304-0597-59df-864c-fbc6c65b39d1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map mul of ede9904075bf: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map mul of ede9904075bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map mul of ede9904075bf construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map mul of ede9904075bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L211-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L211-L224

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) {a q : Ω}
    (ha : a ∈ chartRing S x (liftChart hxy I)) (hq : q ∈ Q.sub (liftChart hxy I)) :
    r (a * q) = red S x y I.1 a * r q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«map_mul_of» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_mul_of_ede9904075bf
