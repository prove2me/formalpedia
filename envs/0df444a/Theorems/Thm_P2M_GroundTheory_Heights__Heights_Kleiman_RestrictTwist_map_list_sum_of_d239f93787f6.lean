-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:14.601869+00:00
-- url     : https://prove2.me/theorems/e70dd212-390c-4da2-831f-9a803db5059d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map list sum of d239f93787f6: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map list sum of d239f93787f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map list sum of d239f93787f6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist map list sum of d239f93787f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L194-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L194-L201

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6 {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (I : Chart y) :
    ∀ l : List Ω, (∀ q ∈ l, q ∈ Q.sub (liftChart hxy I)) → r l.sum = (l.map r).sum
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«map_list_sum_of» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_map_list_sum_of_d239f93787f6
