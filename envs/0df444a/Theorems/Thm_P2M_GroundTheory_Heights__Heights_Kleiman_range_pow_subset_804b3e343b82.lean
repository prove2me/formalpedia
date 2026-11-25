-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_range_pow_subset_804b3e343b82
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_range_pow_subset_804b3e343b82
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:48.042019+00:00
-- url     : https://prove2.me/theorems/b08fc276-bddf-5ae9-9f24-ae712b6f5186
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman range pow subset 804b3e343b82: P2 M Ground Theory Heights  Heights Kleiman range pow subset 804b3e343b82
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman range pow subset 804b3e343b82 construction uses the P2 M Ground Theory Heights  Heights Kleiman range pow subset 804b3e343b82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L101-L112

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_range_pow_subset_804b3e343b82 (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) {q : Ω} (hq : q ∈ Set.range η ^ n) : q ∈ (B.pow n).sub K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«range_pow_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_range_pow_subset_804b3e343b82
