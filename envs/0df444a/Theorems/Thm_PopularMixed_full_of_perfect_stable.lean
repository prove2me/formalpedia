-- Prove2me | Theorems.Thm_PopularMixed_full_of_perfect_stable
-- name    : PopularMixed.full_of_perfect_stable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:40.905842+00:00
-- url     : https://prove2.me/theorems/85951d31-ca8c-4dbe-b1e8-9553a325c679
-- title:
--   Section 3 — under a perfect stable matching, popular fractional matchings fully match every vertex
-- statement:
--   Let $G$ admit a perfect stable matching. Then every popular fractional matching $\vec x\in\mathcal P_G$ fully matches every vertex to genuine neighbours:
--   $$\sum_{b}x(a,b)=1\ \ \forall a\in A,\qquad \sum_{a}x(a,b)=1\ \ \forall b\in B,$$
--   that is, $x(u,\ell(u))=0$ for every $u$. Otherwise $\Delta(\vec x,S)<0$ for any stable matching $S$.
--
--   This is the source of the bound $\alpha^x_u\ge-1$ in Section 3, and hence of $r_a,r_b\in[0,1]$.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 3, PDF p.6 (paragraph after Theorem 3.1) and footnote 2.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Section 3, PDF p.6 with
footnote 2: if `G` admits a perfect stable matching, then every `x ∈ P_G` "has to fully match
every vertex in `A ∪ B` to genuine neighbors, otherwise we have `Δ(x, S) < 0` where `S` is any
stable matching".

**Formalization Note.** "Fully matched to genuine neighbours" is `Σ_v x(u,v) = 1`, i.e. the
last-resort coordinate `x(u, ℓ(u))` is `0`. -/
theorem full_of_perfect_stable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (hG : G.HasPerfectStableMatching) (x : A → B → ℝ) (hx : G.InPG x) :
    (∀ a, ∑ b, x a b = 1) ∧ ∀ b, ∑ a, x a b = 1 := by sorry

end PopularMixed
