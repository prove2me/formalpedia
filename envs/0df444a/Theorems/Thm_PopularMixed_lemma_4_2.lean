-- Prove2me | Theorems.Thm_PopularMixed_lemma_4_2
-- name    : PopularMixed.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:47.744093+00:00
-- url     : https://prove2.me/theorems/4956b430-72fc-4608-858b-36f9ae2c3d69
-- title:
--   Lemma 4.2 — $f$ maps $\mathcal P_G$ into $\mathcal P_H$
-- statement:
--   For every popular fractional matching $\vec x\in\mathcal P_G$, the vector $f(\vec x)$ is a popular fractional matching in $H$:
--   $$\vec x\in\mathcal P_G\implies f(\vec x)\in\mathcal P_H .$$
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: H = (V ∪ V′, E′), V = A_0 ∪ B_1, V′ = B_0 ∪ A_1; u_{1−i} added as u_i's least preferred neighbour → G.double : Instance (A ⊕ B) (B ⊕ A); u_{1−i} gets rank topA/topB = 1 + the largest rank in u's list; reason: relabelling of the vertex sets; the extra rank is below every neighbour, as on PDF p.11
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 4.2, PDF p.11.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional
import Definitions.Def_PopularMixed_Double

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 4.2, PDF p.11: "For any
popular fractional matching `x` in `G`, the vector `f(x)` is a popular fractional matching in
`H`." -/
theorem lemma_4_2 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (x : A → B → ℝ) (hx : G.InPG x) :
    G.double.InPG (fMap x) := by sorry

end PopularMixed
