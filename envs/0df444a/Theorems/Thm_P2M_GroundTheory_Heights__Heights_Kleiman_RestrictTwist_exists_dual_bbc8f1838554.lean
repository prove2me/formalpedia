-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:08:57.191516+00:00
-- url     : https://prove2.me/theorems/506e1e61-5e57-4408-a61c-6a7171436819
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists dual bbc8f1838554: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists dual bbc8f1838554
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists dual bbc8f1838554 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists dual bbc8f1838554 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L172-L184

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554 {x : Fin (N + 1) → Ω} (Q : LineBundle S x) (I : Chart x) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ Q.sub I ∧ ∀ a ∈ Q.sub I, p.2 * a ∈ chartRing S x I) ∧
      (l.map fun p => p.1 * p.2).sum = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«exists_dual» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_dual_bbc8f1838554
