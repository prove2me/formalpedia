-- Prove2me | Theorems.Thm_RandTreeUniv_lemma_2_8
-- name    : RandTreeUniv.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:07.983203+00:00
-- url     : https://prove2.me/theorems/5a83348f-a94a-4456-9edf-aa97f5b560b2
-- title:
--   Lemma 2.8 — $(f,A_1,B_1)$-matchings in $(f,A_1,B_1,\eta,t)$-expanders
-- statement:
--   If a bipartite graph $(A,B)$ is an $(f,A_1,B_1,\eta,t)$-expander (Definition 2.7), then there is an $(f,A_1,B_1)$-matching from $A$ to $B$: an $f$-matching from $A$ to $B$ in which every star centred at a vertex of $A_1$ has all its leaves in $B_1$.
--
--   It generalises Montgomery's Lemma 3.32 (the case $A_1=B_1=\emptyset$) and is used in the absorption steps of §6.
--
--   Differences from the source:
--   - encoding: bipartite graph (A, B) → relation r : A → B → Prop on finite types; reason: same objects
--   - encoding: the neighbourhood of A₁ in the f-matching lies inside B₁ → the leaf set of the star at every v ∈ A₁ is contained in B₁; reason: same condition
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 2.8, p.11 (PDF 12)

import Mathlib
import Definitions.Def_RandTreeUniv_IsFMatching
import Definitions.Def_RandTreeUniv_IsExpander

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Lemma 2.8** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.11 (PDF 12)). If a bipartite graph `(A, B)` is an
`(f, A₁, B₁, η, t)`-expander, then there is an `(f, A₁, B₁)`-matching from `A` to `B`: an
`f`-matching from `A` to `B` in which the neighbourhood of `A₁` lies entirely inside `B₁`.

**Formalization Note** The bipartite graph is `r : A → B → Prop` on finite parts. The expander
predicate carries every condition of Definition 2.7, including `1 ≤ η ≤ t`, `|A₁| ≤ η`,
`f(A) = |B|` and `f ≥ 1`. The star at `v` has leaf set `S v`; "the neighbourhood of `A₁` in the
`f`-matching lies inside `B₁`" is `S v ⊆ B₁` for `v ∈ A₁`. -/
theorem lemma_2_8 {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) (f : A → ℕ)
    (A₁ : Finset A) (B₁ : Finset B) (η t : ℕ) (hexp : IsExpander r f A₁ B₁ η t) :
    ∃ S : A → Finset B, IsFMatching r f S ∧ ∀ v ∈ A₁, S v ⊆ B₁ := by sorry

end RandTreeUniv
