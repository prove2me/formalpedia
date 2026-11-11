-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_6
-- name    : SwitchingStable.Universal.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:18.984084+00:00
-- url     : https://prove2.me/theorems/563f72df-3e9f-4dc4-a65a-655b220e8286
-- title:
--   Lemma 6 — Stable-partner promotion
-- statement:
--   For a complete strict market $I$, put every agent's stable partners first in their original relative order and retain the original order among all others. Call the result $I^\star$. Then
--   $$\mathrm{Stab}(I)\subseteq\mathrm{Stab}(I^\star),$$
--   and both instances have exactly the same stable pairs and ordered stable-partner lists, on both sides. The reconstructed strict orders and the stable-partners-first property are included explicitly. This supports working in the promoted market without asserting equality of its stable set with the original one.
--
--   Differences from the source:
--   - encoding: The instance obtained by stable-partner promotion → The unique rank bijections realizing the prescribed stable-first comparison order; reason: Finite order reconstruction is total; its exact comparison property is proved in the conclusion rather than assumed.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 5, PDF p. 6, Lemma 6

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_6 {n : ℕ} (I : StableMatching.Instance n) :
    HasPromotedOrders I ∧
    (∀ μ : StableMatching.Matching n, I.IsStable μ → (promote I).IsStable μ) ∧
    (∀ u, StableCount.manPartners (promote I) u = StableCount.manPartners I u) ∧
    (∀ v, StableCount.womanPartners (promote I) v = StableCount.womanPartners I v) ∧
    (∀ u, partners (promote I) u = partners I u) ∧
    (∀ v u h, u ∈ StableCount.womanPartners I v → h ∈ StableCount.womanPartners I v →
      ((promote I).womanPrefers v u h ↔ I.womanPrefers v u h)) ∧
    StablePartnersFirst (promote I) := by sorry

end SwitchingStable.Universal
