-- Prove2me | Theorems.Thm_PopularMixed_theorem_4_1
-- name    : PopularMixed.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:35.126979+00:00
-- url     : https://prove2.me/theorems/10e4f4b3-6078-4bd4-a208-b37888e47600
-- title:
--   Theorem 4.1 and Lemma 4.4 — $\mathcal P_G$ is half-integral
-- statement:
--   Let $G=(A\cup B,E)$ be any instance with strict preference lists. Every $\vec x\in\mathcal P_G$ is a convex combination $\vec x=\sum_{i=1}^r\lambda_i\vec q_i$ ($\lambda_i\ge0$, $\sum_i\lambda_i=1$) of popular half-integral matchings $\vec q_1,\dots,\vec q_r$ of $G$ (Lemma 4.4). Hence (Theorem 4.1)
--   $$\mathcal P_G=\operatorname{conv}\{\vec q\in\mathcal P_G:\ \vec q\ \text{half-integral}\}.$$
--
--   This is the paper's main polyhedral result; combined with the decomposition of a half-integral matching into two matchings it gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - reading: "P_G is half-integral" (Theorem 4.1), via Lemma 4.4 → G.PG = convexHull ℝ {q | G.InPG q ∧ IsHalfIntegral q}; reason: ⊆ is Lemma 4.4 and ⊇ is the convexity of P_G; for a polytope this is half-integrality. IsHalfIntegral is on genuine edges; the last-resort coordinates of such a q are then also in {0, 1/2, 1}
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Theorem 4.1, PDF p.10; Lemma 4.4, PDF p.11, proof PDF p.12.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Theorem 4.1 (PDF p.10) and
Lemma 4.4 (PDF p.11, proof p.12): "The popular fractional matching polytope `P_G` in
`G = (A∪B,E)` is half-integral." "Let `x ∈ P_G`. Then `x = Σ_{i=1}^r λ_i q_i`, where `q_1,…,q_r`
are popular half-integral matchings in `G` and `λ_i ≥ 0` for `1 ≤ i ≤ r` along with
`Σ_i λ_i = 1`."

**Formalization Note.** Stated as `P_G = conv {q ∈ P_G : q half-integral}`: the inclusion `⊆` is
Lemma 4.4, and `⊇` is the convexity of `P_G`; together they are "`P_G` is half-integral". -/
theorem theorem_4_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    G.PG = convexHull ℝ {q | G.InPG q ∧ IsHalfIntegral q} := by sorry

end PopularMixed
