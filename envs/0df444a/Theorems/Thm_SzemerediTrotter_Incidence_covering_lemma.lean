-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_covering_lemma
-- name    : SzemerediTrotter.Incidence.covering_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T11:13:51.5993+00:00
-- url     : https://prove2.me/theorems/34abcaaf-8f0b-415e-869c-065240c38467
-- title:
--   Section 2, Lemma (covering lemma) — squares with between $r_1$ and $r_2$ points covering $n/16$ points
-- statement:
--   Fix coordinate axes in the plane; squares have sides parallel to them. Let $r_1, r_2$ be integers with
--
--   $$1 \le r_1, \qquad r_2 \ge 256\, r_1,$$
--
--   and let $\mathcal P$ be a set of $n \ge r_1$ points in the plane. Then there exists a finite family $\mathcal Q$ of squares of positive side length such that
--
--   1. no point of the plane lies in the interior of more than one square of $\mathcal Q$;
--   2. each square of $\mathcal Q$ contains at least $r_1$ and at most $r_2$ points of $\mathcal P$;
--   3. at least $n/16$ of the points of $\mathcal P$ are covered by the squares of $\mathcal Q$.
--
--   This is the covering lemma of Szemerédi and Trotter, proved in their earlier paper *A combinatorial distinction between the Euclidean and projective planes*; it is the principal tool at the end of the proof of Theorem 1, where it localises the crossing pattern of two nearly perpendicular families of lines.
--
--   **Formalization Note** The paper states the lemma for arbitrary integers $r_1, r_2$ with $r_2 \ge 256 r_1$ and any $n$. As printed it fails in degenerate cases: if $0 < n < r_1$ no square contains $r_1$ points, yet a positive number $n/16$ of points must be covered; if $r_1 = r_2 = 0$ and $n > 0$, no square may contain a point. The hypotheses $1 \le r_1$ and $r_1 \le n$ are therefore added (with $r_1, r_2$ natural numbers); in the paper's application $r_1 = d_A/M^4$ is large and $n$ is far larger. A square is a triple $(a, b, s)$ with $s > 0$ (see the squares definition); "contains" and "covered" use the closed square and "interior" the open square; condition 1 is pairwise disjointness of the open squares of distinct members of $\mathcal Q$. The bound $n/16$ is compared over $\mathbb R$.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 382, Section 2, Lemma (covering lemma); proof in [7] Szemerédi, Trotter, A combinatorial distinction between the Euclidean and projective planes

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences
import Definitions.Def_SzemerediTrotter_Incidence_squares

namespace SzemerediTrotter.Incidence

/-- Section 2, Lemma (covering lemma), p. 382, with the non-degeneracy hypotheses
`1 ≤ r₁ ≤ n` added. -/
theorem covering_lemma (r₁ r₂ : ℕ) (h256 : 256 * r₁ ≤ r₂) (P : Finset Plane)
    (hr₁ : 1 ≤ r₁) (hr₁n : r₁ ≤ P.card) :
    ∃ Q : Finset (ℝ × ℝ × ℝ),
      (∀ q ∈ Q, 0 < q.2.2) ∧
      (∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → Disjoint (openSquare q) (openSquare q')) ∧
      (∀ q ∈ Q, r₁ ≤ pointsInSquare P q ∧ pointsInSquare P q ≤ r₂) ∧
      (P.card : ℝ) / 16 ≤ (coveredPoints P Q : ℝ) := by sorry

end SzemerediTrotter.Incidence
