-- Prove2me | Theorems.Thm_PopularMixed_lemma_4_3
-- name    : PopularMixed.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:07.194292+00:00
-- url     : https://prove2.me/theorems/d67681aa-6c73-4c36-8a7b-10afdaaf4f2d
-- title:
--   Lemma 4.3 — $h$ maps $\mathcal P_H$ into $\mathcal P_G$
-- statement:
--   For every popular fractional matching $\vec z\in\mathcal P_H$, the vector $h(\vec z)$ is a popular fractional matching in $G$:
--   $$\vec z\in\mathcal P_H\implies h(\vec z)\in\mathcal P_G .$$
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: H = (V ∪ V′, E′), V = A_0 ∪ B_1, V′ = B_0 ∪ A_1; u_{1−i} added as u_i's least preferred neighbour → G.double : Instance (A ⊕ B) (B ⊕ A); u_{1−i} gets rank topA/topB = 1 + the largest rank in u's list; reason: relabelling of the vertex sets; the extra rank is below every neighbour, as on PDF p.11
--   - encoding: h(z)(u,ℓ(u)) = z(u_0,u_1) → hMap z gives the genuine-edge coordinates; the last-resort coordinate is 1 − Σ_v h(z)(u,v); reason: the two agree whenever the last resorts of u_0, u_1 carry weight 0 in z, which holds for every z ∈ P_H (H has a perfect stable matching, Lemma 4.1); the statement only concerns z ∈ P_H
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 4.3, PDF p.11.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional
import Definitions.Def_PopularMixed_Double

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 4.3, PDF p.11: "For any
popular fractional matching `z` in `H`, the vector `h(z)` is a popular fractional matching in
`G`." -/
theorem lemma_4_3 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (z : A ⊕ B → B ⊕ A → ℝ) (hz : G.double.InPG z) :
    G.InPG (hMap z) := by sorry

end PopularMixed
