-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:09.194907+00:00
-- url     : https://prove2.me/theorems/529054de-5336-447f-a01b-316ef97589a1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed C injective bbfdf92a6e8b: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed C injective bbfdf92a6e8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed C injective bbfdf92a6e8b construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed C injective bbfdf92a6e8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L155-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
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
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b (n : ℕ) : Function.Injective (M.embedC c n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«embedC_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b
