-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_2_6
-- name    : RandTreeUniv.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:20.593306+00:00
-- url     : https://prove2.me/theorems/7d8cc57a-dc16-4b8a-b2ff-7b8d60a2dc57
-- title:
--   Theorem 2.6 (Montgomery) — Hall's theorem for $f$-matchings
-- statement:
--   Let $(A,B)$ be a bipartite graph and $f:A\to\mathbb N$ a function with positive integer values. Suppose that for every $U\subseteq A$
--
--   $$
--   |N(U)|\ge f(U)=\sum_{v\in U}f(v).
--   $$
--
--   Then there is an $f$-matching from $A$ to $B$: vertex-disjoint stars $(S_v)_{v\in A}$, the star $S_v$ centred at $v$ with $f(v)$ leaves in $B$.
--
--   This is the many-to-one extension of Hall's criterion (Montgomery 2019, Theorem 3.31); Lemma 2.8 reduces to it.
--
--   Differences from the source:
--   - encoding: bipartite graph with parts A, B → relation r : A → B → Prop on finite types; reason: same objects
--   - encoding: f : A → ℕ, ℕ the positive integers (§2.1) → f : A → ℕ with f v ≥ 1; reason: same functions
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 2.6, p.11 (PDF 12) (Theorem 3.31 in Montgomery 2019)

import Mathlib
import Definitions.Def_RandTreeUniv_bipNbr
import Definitions.Def_RandTreeUniv_IsFMatching

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Theorem 2.6** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.11 (PDF 12); Theorem 3.31 in Montgomery 2019). Fix a bipartite
graph with parts `A`, `B` and a function `f : A → ℕ` (positive integers). Suppose that, for every
subset `U ⊆ A`, `|N(U)| ≥ f(U) = ∑_{v ∈ U} f(v)`. Then there is an `f`-matching from `A` to `B`.

**Formalization Note** The bipartite graph is `r : A → B → Prop` on finite parts; `ℕ` in the
paper is the positive integers (§2.1), so `f ≥ 1` is a hypothesis. -/
theorem theorem_2_6 {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) (f : A → ℕ)
    (hf : ∀ v, 1 ≤ f v) (hHall : ∀ U : Finset A, ∑ v ∈ U, f v ≤ (bipNbr r U).card) :
    ∃ S : A → Finset B, IsFMatching r f S := by sorry

end RandTreeUniv
