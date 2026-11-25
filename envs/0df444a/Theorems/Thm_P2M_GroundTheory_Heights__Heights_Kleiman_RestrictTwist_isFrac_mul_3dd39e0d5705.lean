-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:18.597081+00:00
-- url     : https://prove2.me/theorems/ff7ce308-ab60-51be-b2bf-f960f1f63110
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac mul 3dd39e0d5705: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac mul 3dd39e0d5705
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac mul 3dd39e0d5705 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac mul 3dd39e0d5705 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L39-L47

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705 {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} {g u : Poly S N} {d : ℕ} (hu : u ∈ monos I)
    (hg : g.IsHomogeneous d) (hud : u.IsHomogeneous d) (h : IsFrac x c I z t) :
    IsFrac x c I (aeval x g / aeval x u * z) (g * t.1, u * t.2.1, d + t.2.2.1, d + t.2.2.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«isFrac_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705
