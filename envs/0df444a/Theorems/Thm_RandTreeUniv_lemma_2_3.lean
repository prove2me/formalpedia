-- Prove2me | Theorems.Thm_RandTreeUniv_lemma_2_3
-- name    : RandTreeUniv.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:07.265276+00:00
-- url     : https://prove2.me/theorems/7e673173-fab1-4ee2-a0a2-999c465343d5
-- title:
--   Lemma 2.3 — Hall for small sets plus joinedness gives a perfect matching
-- statement:
--   Let $G$ be a bipartite graph with parts $A$ and $B$ of equal size, and let $t$ be a positive integer such that
--
--   1. for every set $U$ with $|U|\le t$ and $U\subseteq A$ or $U\subseteq B$, $|N(U)|\ge|U|$;
--   2. for all $U\subseteq A$ and $W\subseteq B$ with $|U|=|W|=t$, there is at least one edge between $U$ and $W$, i.e. $e(U,W)\ge1$.
--
--   Then $G$ contains a perfect matching from $A$ to $B$.
--
--   This version of Hall's theorem only asks for Hall's condition on small sets, paid for by the joinedness condition 2. It is the matching tool used to extend partial embeddings in §5 and §6.
--
--   Differences from the source:
--   - encoding: bipartite graph with parts A, B; perfect matching from A to B → relation r : A → B → Prop on finite types; bijection e : A ≃ B with r a (e a); reason: same objects
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 2.3, p.10 (PDF 11)

import Mathlib
import Definitions.Def_RandTreeUniv_bipNbr

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Lemma 2.3** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.10 (PDF 11)). Fix a bipartite graph `G` with equal parts `A` and `B`
and a positive integer `t` such that:
(i) for all sets `U` of size at most `t` with `U ⊆ A` or `U ⊆ B`, `|N(U)| ≥ |U|`;
(ii) for all sets `U ⊆ A` and `W ⊆ B` of size `t`, `e(U, W) ≥ 1`.
Then `G` contains a perfect matching from `A` to `B`.

**Formalization Note** The bipartite graph is `r : A → B → Prop` on finite parts with
`|A| = |B|`; `N(U)` is `bipNbr r U` (resp. `bipNbr (flip r) U`). A perfect matching from `A` to
`B` is a bijection `e : A ≃ B` with `r a (e a)` for every `a`. -/
theorem lemma_2_3 {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop)
    (hAB : Fintype.card A = Fintype.card B) (t : ℕ) (ht : 0 < t)
    (hA : ∀ U : Finset A, U.card ≤ t → U.card ≤ (bipNbr r U).card)
    (hB : ∀ U : Finset B, U.card ≤ t → U.card ≤ (bipNbr (flip r) U).card)
    (hjoin : ∀ (U : Finset A) (W : Finset B), U.card = t → W.card = t → ∃ a ∈ U, ∃ b ∈ W, r a b) :
    ∃ e : A ≃ B, ∀ a, r a (e a) := by sorry

end RandTreeUniv
