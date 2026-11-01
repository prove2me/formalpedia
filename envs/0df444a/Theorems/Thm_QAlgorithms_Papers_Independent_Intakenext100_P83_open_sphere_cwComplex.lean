-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P83_open_sphere_cwComplex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P83.open_sphere_cwComplex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:11:05.165074+00:00
-- url     : https://prove2.me/theorems/9081a7d7-d495-43ad-8054-bb9507c5e7db
-- title:
--   Open subspaces of spheres admit CW structures
-- statement:
--   Let $n\ge1$, and give the Euclidean unit sphere $S^{n-1}\subset\mathbb R^n$ its usual topology. Every open subset $U\subseteq S^{n-1}$, including the empty subset, admits a CW-complex structure compatible with its subspace topology:
--
--   $$
--   \exists\text{ a CW structure on }U.
--   $$
--
--   This asserts a CW structure on the given space, which is stronger than merely having CW homotopy type. It provides the sphere-subspace input used later for the disk-cover comparison.
-- source:
--   Two-Categorical Bundles and Their Classifying Spaces, arXiv:math/0612549v2, PDF p. 54, Theorem 7.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P83

open CategoryTheory

open scoped Simplicial

namespace QAlgorithms.Papers.Independent.Intakenext100.P83

universe u v

/-- Theorem 7.6 (Whitney), PDF p. 54. Every open subspace of the Euclidean
sphere `S^(n-1)` has an actual CW structure in its existing subspace topology.
`n ≥ 1`; the empty open subspace is included. We ask for a CW structure on
`univ` of the subtype, so no ambient closedness condition is imposed on `U`. -/
theorem open_sphere_cwComplex (n : ℕ) (hn : 1 ≤ n)
    (U : Set {x : EuclideanSpace ℝ (Fin n) // x ∈ Metric.sphere 0 1})
    (hU : IsOpen U) :
    Nonempty (Topology.CWComplex (Set.univ : Set U)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P83
