-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_domRing_self_le_54dbb7098c5f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_domRing_self_le_54dbb7098c5f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:29.337841+00:00
-- url     : https://prove2.me/theorems/721d769b-ad5a-5597-80a1-6bc55a093668
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman dom Ring self le 54dbb7098c5f: P2 M Ground Theory Heights  Heights Kleiman dom Ring self le 54dbb7098c5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman dom Ring self le 54dbb7098c5f construction uses the P2 M Ground Theory Heights  Heights Kleiman dom Ring self le 54dbb7098c5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L358-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L358-L368

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
open MvPolynomial Filter
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_domRing_self_le_54dbb7098c5f {i : Fin (N + 1)} (hi : x i ≠ 0) :
    domRing S x x i ⊆ chartRing S x (singleChart hi) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«domRing_self_le» := P2M_GroundTheory_Heights__Heights_Kleiman_domRing_self_le_54dbb7098c5f
