-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:04.48568+00:00
-- url     : https://prove2.me/theorems/a4b25ebf-8872-40c8-aa2f-62a12f100688
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Generated sub ne bot cb59329d6f45: P2 M Ground Theory Heights  Heights Kleiman Restrict Generated sub ne bot cb59329d6f45
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Generated sub ne bot cb59329d6f45 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Generated sub ne bot cb59329d6f45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L61-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45 (Q' : LineBundle S y) (J : Chart y) : Q'.toSubSystem.sub J ≠ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictGenerated».«sub_ne_bot» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_sub_ne_bot_cb59329d6f45
