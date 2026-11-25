-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:08.494854+00:00
-- url     : https://prove2.me/theorems/71bcb4ec-a942-42d6-9941-91a0e2d3e95c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac add c90e5fd76ad2: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac add c90e5fd76ad2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac add c90e5fd76ad2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist is Frac add c90e5fd76ad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L23-L37

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2 {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z z' : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (hI : ∀ s ∈ monos (S := S) I, aeval x s ≠ 0)
    (h : IsFrac x c I z t) (h' : IsFrac x c I z' t') :
    IsFrac x c I (z + z')
      (t.1 * t'.2.1 + t.2.1 * t'.1, t.2.1 * t'.2.1, t.2.2.1 + t'.2.2.1, t.2.2.2 + t'.2.2.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«isFrac_add» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
