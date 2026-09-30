-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_good_intersections_bound
-- name    : SzemerediTrotter.Incidence.good_intersections_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:51:45.307411+00:00
-- url     : https://prove2.me/theorems/91071057-a47e-4f6a-8249-12fc85e8ab97
-- title:
--   Section 3, display on p. 383 — $\sum_i \binom{d_i}{2} \le \binom{t}{2}$ and $\frac{I^2}{2n} - \frac I2 \le \frac{t^2}{2}$
-- statement:
--   Let $\mathcal P$ be a finite set of $n$ points in the Euclidean plane and $\mathcal L$ a family of $t$ distinct lines. For a point $p$ let $d(p)$ be the number of lines of $\mathcal L$ through $p$, and let $I = I(\mathcal P,\mathcal L)$ be the number of incidences. Then
--
--   1. the number of pairs of lines of $\mathcal L$ that meet at a point of $\mathcal P$ is at most the number of all pairs of lines:
--   $$\sum_{p \in \mathcal P} \binom{d(p)}{2} \le \binom{t}{2};$$
--   2. consequently,
--   $$\frac{I^2}{2n} - \frac{I}{2} \le \frac{t^2}{2}.$$
--
--   No relation between $n$ and $t$ is assumed. In Szemerédi and Trotter's proof of Theorem 1, the quantity $\sum_i \binom{d_i}{2}$ counts the **good intersections** (pairs of lines meeting at a point of $\mathcal P$); this inequality is the first step of the proof and yields that $t$ is large compared with $\sqrt n$ in a counterexample.
--
--   **Formalization Note** The binomial coefficients are natural-number `Nat.choose`; the second inequality is stated over $\mathbb R$ with all counts cast to real numbers. When $n = 0$, Lean's convention $x/0 = 0$ applies; then $I = 0$ and the inequality reads $0 \le t^2/2$.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 383, Section 3, display on p. 383 (good intersections; the chain up to (1/2n)I² − ½I)

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences

namespace SzemerediTrotter.Incidence

/-- Section 3, display on p. 383: for any finite set `𝒫` of points and any finite family `ℒ`
of distinct lines, `∑ᵢ C(dᵢ, 2) ≤ C(t, 2)` and `I²/(2n) − I/2 ≤ t²/2`. -/
theorem good_intersections_bound (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) :
    (∑ p ∈ P, (degree L p).choose 2 ≤ L.card.choose 2) ∧
    ((incidences P L : ℝ) ^ 2 / (2 * (P.card : ℝ)) - (incidences P L : ℝ) / 2
      ≤ (L.card : ℝ) ^ 2 / 2) := by sorry

end SzemerediTrotter.Incidence
