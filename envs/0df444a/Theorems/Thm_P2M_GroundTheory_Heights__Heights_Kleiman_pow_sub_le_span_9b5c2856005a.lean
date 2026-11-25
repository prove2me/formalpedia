-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_sub_le_span_9b5c2856005a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pow_sub_le_span_9b5c2856005a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:34.796729+00:00
-- url     : https://prove2.me/theorems/4f85ff10-f3ad-4312-afbf-59625ba6a5b5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman pow sub le span 9b5c2856005a: P2 M Ground Theory Heights  Heights Kleiman pow sub le span 9b5c2856005a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman pow sub le span 9b5c2856005a construction uses the P2 M Ground Theory Heights  Heights Kleiman pow sub le span 9b5c2856005a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L75-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L75-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
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
open MvPolynomial Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable {G B : SubSystem S x Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pow_sub_le_span_9b5c2856005a (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) : (B.pow n).sub K ≤ Submodule.span (chartRing S x K) (Set.range η ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pow_sub_le_span» := P2M_GroundTheory_Heights__Heights_Kleiman_pow_sub_le_span_9b5c2856005a
