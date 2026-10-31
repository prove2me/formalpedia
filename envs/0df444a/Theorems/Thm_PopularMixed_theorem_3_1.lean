-- Prove2me | Theorems.Thm_PopularMixed_theorem_3_1
-- name    : PopularMixed.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:48.955564+00:00
-- url     : https://prove2.me/theorems/0a84acf5-d137-4490-8c0c-7d9139e938d6
-- title:
--   Theorem 3.1 — $\mathcal P_G$ is integral when $G$ admits a perfect stable matching
-- statement:
--   Let $G=(A\cup B,E)$ be an instance of the stable marriage problem with strict preference lists such that $G$ admits a perfect stable matching. Then $\mathcal P_G$ is integral:
--   $$\mathcal P_G=\operatorname{conv}\{I_M:\ M\ \text{a popular matching of }G\}.$$
--
--   This is the special case from which half-integrality in general (Theorem 4.1) is derived, through the doubled instance $H$.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - reading: "P_G is integral" → G.PG = convexHull ℝ {I_M : M popular}; reason: P_G is a polytope, so integral means it is the convex hull of its integral points; those are exactly the I_M of popular matchings (an integral point of M_G is some I_M, and I_M ∈ P_G iff M is popular); the proof establishes this form (PDF p.10)
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Theorem 3.1, PDF p.6; proof concluded PDF p.10.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Theorem 3.1, PDF p.6 (proof
ends PDF p.10): "Let `G = (A ∪ B, E)` be an instance of the stable marriage problem with strict
preference lists such that `G` admits a perfect stable matching. Then `P_G` is integral."

**Formalization Note.** "Integral" is stated as: `P_G` is the convex hull of the incidence
vectors of the popular matchings of `G`, which are exactly the integral points of `P_G`; this is
what the proof establishes ("every popular fractional matching in `G` can be expressed as a
convex combination of … popular matchings in `G`", PDF p.10). -/
theorem theorem_3_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (hG : G.HasPerfectStableMatching) :
    G.PG = convexHull ℝ {y | ∃ M, G.IsPopular M ∧ y = incid M} := by sorry

end PopularMixed
