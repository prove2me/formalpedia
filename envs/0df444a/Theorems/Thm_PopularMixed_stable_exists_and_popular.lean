-- Prove2me | Theorems.Thm_PopularMixed_stable_exists_and_popular
-- name    : PopularMixed.stable_exists_and_popular
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:35.421008+00:00
-- url     : https://prove2.me/theorems/09e56c1c-c26a-42a3-87df-cfd984bef6d9
-- title:
--   Section 1 — stable matchings exist and every stable matching is popular
-- statement:
--   Let $G=(A\cup B,E)$ be any instance with strict, possibly incomplete preference lists. Then
--
--   1. $G$ has a stable matching, and
--   2. every stable matching $S$ of $G$ is popular: $\Delta(S,M')\ge0$ for every matching $M'$.
--
--   These are the two classical facts the paper cites (Gale–Shapley; Gärdenfors). The first makes $\mathcal P_G$ nonempty; the second is used for the stable matchings of $G$ and of the doubled instance $H$ in Sections 3 and 4.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 1, PDF p.1 (citing Gale–Shapley [16] and Gärdenfors [18]).

import Mathlib
import Definitions.Def_PopularMixed_Model

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Section 1, PDF p.1: "The
existence of stable matchings and the Gale-Shapley algorithm [16] to find one are classical
results in algorithms. It is easy to show that every stable matching is popular [18]."

Both facts, for every instance with strict and possibly incomplete preference lists and sides of
any sizes. -/
theorem stable_exists_and_popular {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    (∃ S, G.IsStable S) ∧ ∀ S, G.IsStable S → G.IsPopular S := by sorry

end PopularMixed
