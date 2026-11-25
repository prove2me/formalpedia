-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:08:48.872229+00:00
-- url     : https://prove2.me/theorems/1370fcf8-1871-540b-8d20-d6fb3d09b0ed
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists is Frac 46d7eee3b227: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists is Frac 46d7eee3b227
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists is Frac 46d7eee3b227 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists is Frac 46d7eee3b227 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L49-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227 {x : Fin (N + 1) → Ω} {c : ℤ} {I : Chart x} {z : Ω}
    (hz : z ∈ twistMod S x c I) : ∃ t, IsFrac (S := S) x c I.1 z t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«exists_isFrac» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
