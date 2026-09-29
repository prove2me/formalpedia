-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_axisSphere_eq
-- name    : RelaxationMethod.LowDim.axisSphere_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:29:11.902537+00:00
-- url     : https://prove2.me/theorems/2851493a-e954-418e-98e0-272f27d6616a
-- title:
--   §2, (1.10) — the equidistant locus is a sphere having $L_r$ as its axis
-- statement:
--   Let $L$ be a nonempty flat of $E_n$ with direction space $V$, and let $p \notin L$. Let $b$ be the orthogonal projection of $p$ onto $L$ and $X = \{x : |x - a| = |p - a| \text{ for every } a \in L\}$ the locus (1.10). Then:
--
--   1. $X$ is the sphere, inside the flat through $b$ normal to $L$, with centre $b$ passing through $p$:
--   $$X = \{x : x - b \in V^{\perp},\ |x - b| = |p - b|\};$$
--   2. $L$ is exactly the set of points equidistant from all points of $X$:
--   $$L = \{a : |x - a| = |p - a| \text{ for every } x \in X\}.$$
--
--   This is the claim of §2 that justifies calling $X$ a spherical surface $S_{n-r-1}$ with axis $L$; it identifies the set on which Theorem 2, Case 2 places the tail of a reflexion sequence.
--
--   **Formalization Note** The flat is an arbitrary nonempty `AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))`; the paper's $0 \leqslant r \leqslant n-1$ follows from $p \notin L$. The orthogonal projection is Mathlib's `EuclideanGeometry.orthogonalProjection`, and "the $(n-r)$-flat normal to $L_r$ at $b$" is written as $x - b \in V^{\perp}$. The dimension count $n - r - 1$ of the sphere is not part of the statement.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 395, §2, (1.10)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_AxisSphere

namespace RelaxationMethod.LowDim

/-- §2, p. 395: for a flat `L` and a point `p ∉ L`, with `b` the orthogonal projection of `p`
onto `L`, the locus (1.10) is the sphere of the flat through `b` normal to `L`, centred at `b`
and passing through `p`; and `L` is exactly the set of points equidistant from all points of
that sphere. -/
theorem axisSphere_eq {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L]
    (p : EuclideanSpace ℝ (Fin n)) (hp : p ∉ L) :
    axisSphere L p =
        {x | x -ᵥ (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) ∈
              L.directionᗮ ∧
            dist x (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) =
              dist p (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n))} ∧
      (L : Set (EuclideanSpace ℝ (Fin n))) =
        {a | ∀ x ∈ axisSphere L p, dist x a = dist p a} := by sorry

end RelaxationMethod.LowDim
