-- Prove2me | Theorems.Thm_PopularMixed_theorem_1_1
-- name    : PopularMixed.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:19.318807+00:00
-- url     : https://prove2.me/theorems/818ee25c-c712-48a6-a878-bf268e9acdc0
-- title:
--   Theorem 1.1 — a max-utility popular mixed matching $\{(M_0,\tfrac12),(M_1,\tfrac12)\}$, pure under a perfect stable matching
-- statement:
--   Let $G=(A\cup B,E)$ be an instance with strict preference lists and let $w$ be a utility function on the edges. Then
--
--   1. $G$ has a max-utility popular mixed matching of the form $\Pi=\{(M_0,\tfrac12),(M_1,\tfrac12)\}$ with $M_0,M_1$ matchings of $G$: $\Pi$ is popular (Definition 2) and
--   $$\sum_i p_i\,w(N_i)\ \le\ \tfrac12\,w(M_0)+\tfrac12\,w(M_1)$$
--   for every popular mixed matching $\Lambda=\{(N_0,p_0),\dots,(N_h,p_h)\}$ of $G$;
--   2. if moreover $G$ admits a perfect stable matching (a stable matching where no vertex is unmatched), then some max-utility popular mixed matching is pure: $\Pi=\{(M,1)\}$ for a matching $M$ of $G$.
--
--   Thus a single random bit suffices to implement a max-utility popular lottery, and none is needed when $G$ has a perfect stable matching.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: mixed matching {(M_0,p_0),…,(M_k,p_k)}, p_i ≥ 0, Σ p_i = 1 → Λ : Finset (A × B) → ℝ, Λ ≥ 0, Σ_M Λ M = 1, Λ M ≠ 0 only for matchings M; reason: repeated matchings are merged; every finite lottery over matchings is such a Λ and conversely
--   - generalization: utility w : E → Q → w : A → B → ℝ; reason: every rational utility on E extends to a real function on A × B (values off E are never read on a matching); the rational statement is the special case
--   - reading: "Π = {(M,1)} for some matching M in G, i.e., Π is pure" → ∃ M, pure M is popular and max-utility; reason: the literal "every max-utility Π is pure" is false when two popular matchings tie; the sentence asserts that the max-utility popular mixed matching can be taken pure
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Theorem 1.1, PDF p.2.

import Mathlib
import Definitions.Def_PopularMixed_Model

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Theorem 1.1, PDF p.2: "Given
an instance `G = (A ∪ B, E)` with strict preference lists and a utility function `w : E → Q`,
`G` always has a max-utility popular mixed matching `Π = {(M0, 1/2), (M1, 1/2)}` where `M0` and
`M1` are matchings in `G`. Moreover, if `G` admits a perfect stable matching, i.e., a stable
matching where no vertex is unmatched, then `Π = {(M,1)}` for some matching `M` in `G`, i.e.,
`Π` is pure."

**Formalization Note.** Popularity of mixed matchings is Definition 2 (`IsPopularMixed`), and
"max-utility" ranges over every popular mixed matching `Λ` (any finite lottery with real
probabilities). The utility is real-valued (`w : A → B → ℝ`; its values off `E` are never
read), which contains the rational case. The second clause is read as: a max-utility popular
mixed matching can be taken pure. -/
theorem theorem_1_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (w : A → B → ℝ) :
    (∃ M₀ M₁, G.IsMatching M₀ ∧ G.IsMatching M₁ ∧ G.IsPopularMixed (half M₀ M₁) ∧
        ∀ Λ, G.IsPopularMixed Λ → utility w Λ ≤ utility w (half M₀ M₁)) ∧
      (G.HasPerfectStableMatching →
        ∃ M, G.IsMatching M ∧ G.IsPopularMixed (pure M) ∧
          ∀ Λ, G.IsPopularMixed Λ → utility w Λ ≤ utility w (pure M)) := by sorry

end PopularMixed
