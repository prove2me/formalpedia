-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_theorem_1
-- name    : SzemerediTrotter.Incidence.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T11:20:04.420105+00:00
-- url     : https://prove2.me/theorems/16b72252-3a40-4101-9932-b0a184530042
-- title:
--   Theorem 1 (Szemerédi–Trotter) — at most $c_1 n^{2/3} t^{2/3}$ incidences when $\sqrt n \le t \le \binom n2$
-- statement:
--   There exists a constant $c_1$ with the following property. Let $\mathcal P$ be a set of $n$ points and $\mathcal L$ a family of $t$ distinct lines in the Euclidean plane, with
--
--   $$\sqrt n \le t \le \binom{n}{2}.$$
--
--   Then the number of incidences between the points of $\mathcal P$ and the lines of $\mathcal L$ satisfies
--
--   $$I(\mathcal P,\mathcal L) \le c_1\, n^{2/3}\, t^{2/3}.$$
--
--   The constant $c_1$ is absolute: it is chosen once, before the point set and the line family. This is the principal theorem of Szemerédi and Trotter (1983), settling a conjecture of Erdős (the case $t = n$ gives at most $c_1 n^{4/3}$ incidences). Their proof shows that $c_1 = 10^{60}$ suffices. The bound is sharp up to the constant, and the theorem underlies the bounds on $k$-rich lines, Beck's theorem and many later incidence results.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)`, a line is an affine subspace with one-dimensional direction, the points form a `Finset` and the lines a `Finset` of affine subspaces (so they are distinct), and the incidence count is the definition `incidences`. The powers $n^{2/3}$ and $t^{2/3}$ are `Real.rpow` of the counts cast to $\mathbb R$. The statement follows the wording of p. 381 ("at most"); the restatement on p. 383 says "less than", which fails for $n = t = 0$ and agrees with this one for $n \ge 1$ after doubling $c_1$.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 381, Theorem 1 (restated and proved in Section 3, p. 383)

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences

namespace SzemerediTrotter.Incidence

/-- Theorem 1 (p. 381; restated and proved in Section 3, p. 383), the Szemerédi–Trotter
incidence bound: there is an absolute constant `c₁` such that `n` points and `t` distinct lines
in the plane with `√n ≤ t ≤ C(n, 2)` have at most `c₁ n^{2/3} t^{2/3}` incidences. -/
theorem theorem_1 :
    ∃ c₁ : ℝ, ∀ (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)),
      (∀ l ∈ L, IsLine l) →
      Real.sqrt (P.card : ℝ) ≤ (L.card : ℝ) →
      L.card ≤ P.card.choose 2 →
      (incidences P L : ℝ) ≤ c₁ * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by sorry

end SzemerediTrotter.Incidence
