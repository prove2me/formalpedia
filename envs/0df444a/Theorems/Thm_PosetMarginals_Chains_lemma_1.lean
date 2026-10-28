-- Prove2me | Theorems.Thm_PosetMarginals_Chains_lemma_1
-- name    : PosetMarginals.Chains.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:35.694981+00:00
-- url     : https://prove2.me/theorems/d07f6a48-a176-4a00-88b0-424d93c79866
-- title:
--   Lemma 1 — minimal elements meet every maximal chain
-- statement:
--   Let $P$ be a finite nonempty poset, and let $M$ be its set of minimal elements. Then $M$ is an antichain, and every maximal chain $C$ contains at least one element of $M$:
--   $$M\text{ is an antichain},\qquad C\in\mathcal C\Longrightarrow C\cap M\ne\varnothing.$$
--
--   This identifies a canonical antichain intersecting all maximal chains, used in the algorithm's selection rule.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 6, Lemma 1; proof p. 34

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Lemma 1, p. 6. -/
theorem lemma_1 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α] :
    IsAntichain (· ≤ ·) {x : α | IsMin x} ∧
      ∀ C : Set α, IsMaxChain (· ≤ ·) C → ∃ x ∈ C, IsMin x := by sorry

end PosetMarginals.Chains
