-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:09.925906+00:00
-- url     : https://prove2.me/theorems/439430ae-a06a-5e3a-bb53-71f5f0a6636d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res add db6472489522: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res add db6472489522
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res add db6472489522 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res add db6472489522 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L237-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L237-L244

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522 {r₁ : Ω → K'} {Q₂ : SubSystem S x Ω} {Q₂' : SubSystem S y K'} {r₂ : Ω → K'}
    (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y) {l : List (Ω × Ω)} {z z' : Ω}
    (hz : ∀ p ∈ l, p.2 * z ∈ Q₂.sub (liftChart hxy I))
    (hz' : ∀ p ∈ l, p.2 * z' ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (z + z') = prodRes r₁ r₂ l z + prodRes r₁ r₂ l z' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«prodRes_add» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_add_db6472489522
