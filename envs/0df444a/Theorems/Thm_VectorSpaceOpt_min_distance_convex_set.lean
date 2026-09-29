-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_distance_convex_set
-- name    : VectorSpaceOpt.min_distance_convex_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:24:55.126317+00:00
-- url     : https://prove2.me/theorems/3414380c-564e-4d59-86ee-c16fdc7a71c2
-- title:
--   Minimum distance to a closed convex set and its variational inequality
-- statement:
--   Let $x$ be a vector in a real Hilbert space $H$ and let $K$ be a **nonempty closed convex** subset of $H$. The theorem makes two claims.
--
--   **1. A unique nearest point exists.**
--
--   $$\exists!\, k_0 \in K \ \text{ such that } \ \|x - k_0\| \le \|x - k\| \quad \text{for all } k \in K.$$
--
--   **2. A variational inequality characterizes it.** For $k_0 \in K$, being that nearest point is equivalent to
--
--   $$\langle x - k_0,\, k - k_0\rangle \le 0 \qquad \text{for all } k \in K.$$
--
--   This extends the projection theorem from subspaces to convex sets, and the extension costs one thing: the orthogonality *equality* of the subspace case weakens to an *inequality*. Geometrically, the angle between the error $x - k_0$ and every feasible direction $k - k_0$ is obtuse — one cannot move from $k_0$ toward any point of $K$ without moving away from $x$. When $K$ happens to be a subspace, applying the inequality to $k_0 \pm k$ recovers the equality.
--
--   Existence and uniqueness are proved as for the projection theorem, with convexity of $K$ supplying the midpoint $(k_i + k_j)/2 \in K$ that the parallelogram-law argument needs.
--
--   **Formalization Note.** The variational characterization is stated for every $k_0 \in K$, not only for the nearest point produced by the first claim; the inequality direction is as displayed and is not symmetric.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.12, Theorem 1, p. 69

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem min_distance_convex_set {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : Set H) (hK : Convex ℝ K) (hKc : IsClosed K) (hKne : K.Nonempty) (x : H) :
    (∃! k₀ : H, k₀ ∈ K ∧ ∀ k ∈ K, ‖x - k₀‖ ≤ ‖x - k‖) ∧
    (∀ k₀ ∈ K, (∀ k ∈ K, ‖x - k₀‖ ≤ ‖x - k‖) ↔ (∀ k ∈ K, ⟪x - k₀, k - k₀⟫ ≤ 0)) := by
  sorry

end VectorSpaceOpt
