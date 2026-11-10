-- Prove2me | Theorems.Thm_RandTreeUniv_corollary_2_4
-- name    : RandTreeUniv.corollary_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:10.142564+00:00
-- url     : https://prove2.me/theorems/dd202af2-1880-42b9-85fc-3c1c02f274d0
-- title:
--   Corollary 2.4 — Hall's condition up to $\lceil n/2\rceil$ suffices
-- statement:
--   Let $G$ be a bipartite graph with parts $A$, $B$ such that $|A|=|B|=n$. Assume that for every set $U\subseteq A$ or $U\subseteq B$ with
--
--   $$
--   |U|\le\lceil n/2\rceil
--   $$
--
--   we have $|N(U)|\ge|U|$. Then $G$ contains a perfect matching.
--
--   Hall's condition for sets up to half the size of a part, checked on both sides, already implies the full condition.
--
--   Differences from the source:
--   - encoding: bipartite graph with parts A, B; perfect matching from A to B → relation r : A → B → Prop on finite types; bijection e : A ≃ B with r a (e a); reason: same objects
--   - encoding: ⌈n/2⌉ → (n + 1) / 2 in ℕ; reason: equal for every natural number n
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Corollary 2.4, p.10 (PDF 11)

import Mathlib
import Definitions.Def_RandTreeUniv_bipNbr

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Corollary 2.4** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.10 (PDF 11)). Fix a bipartite graph `G` with parts `A`, `B` such
that `|A| = |B| = n`. Assume that, for every set `U ⊆ A` or `U ⊆ B` of size `|U| ≤ ⌈n/2⌉`,
`|N(U)| ≥ |U|`. Then `G` contains a perfect matching.

**Formalization Note** The bipartite graph is `r : A → B → Prop` on finite parts; `⌈n/2⌉` is
`(n + 1) / 2` in `ℕ`. A perfect matching is a bijection `e : A ≃ B` with `r a (e a)` for all `a`. -/
theorem corollary_2_4 {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) (n : ℕ)
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hHallA : ∀ U : Finset A, U.card ≤ (n + 1) / 2 → U.card ≤ (bipNbr r U).card)
    (hHallB : ∀ U : Finset B, U.card ≤ (n + 1) / 2 → U.card ≤ (bipNbr (flip r) U).card) :
    ∃ e : A ≃ B, ∀ a, r a (e a) := by sorry

end RandTreeUniv
