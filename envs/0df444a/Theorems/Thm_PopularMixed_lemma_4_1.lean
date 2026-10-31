-- Prove2me | Theorems.Thm_PopularMixed_lemma_4_1
-- name    : PopularMixed.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:28.118518+00:00
-- url     : https://prove2.me/theorems/a487c026-1d41-43d3-94fb-6a0631cf21a2
-- title:
--   Lemma 4.1 — the doubled instance $H$ admits a perfect stable matching
-- statement:
--   For every instance $G=(A\cup B,E)$ with strict preference lists, the doubled instance $H$ of Section 4 admits a perfect stable matching.
--
--   The proof restricts a stable matching of $H$ to $E_0$ and $E_1$ and uses that all stable matchings of $G$ match the same vertices (Gale–Sotomayor). Lemma 4.1 is what allows Theorem 3.1 to be applied to $H$.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: H = (V ∪ V′, E′), V = A_0 ∪ B_1, V′ = B_0 ∪ A_1; u_{1−i} added as u_i's least preferred neighbour → G.double : Instance (A ⊕ B) (B ⊕ A); u_{1−i} gets rank topA/topB = 1 + the largest rank in u's list; reason: relabelling of the vertex sets; the extra rank is below every neighbour, as on PDF p.11
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 4.1, PDF p.11.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Double

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 4.1, PDF p.11: "`H`
admits a perfect stable matching", for the doubled instance `H` of Section 4, for every
instance `G` with strict preference lists. -/
theorem lemma_4_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    G.double.HasPerfectStableMatching := by sorry

end PopularMixed
