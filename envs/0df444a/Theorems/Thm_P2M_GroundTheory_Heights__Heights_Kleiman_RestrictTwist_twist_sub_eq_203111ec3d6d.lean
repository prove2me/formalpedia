-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:44.34553+00:00
-- url     : https://prove2.me/theorems/c18183fd-437c-5ae9-b3cc-aa126722e1c1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist sub eq 203111ec3d6d: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist sub eq 203111ec3d6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist sub eq 203111ec3d6d construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist sub eq 203111ec3d6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L150-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L150-L156

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d {L : Type w} [Field L] [Algebra S L] {z : Fin (N + 1) → L}
    (F Q : SubSystem S z L) (I : Chart z) : (F.twist Q).sub I = Q.sub I * F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«twist_sub_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d
