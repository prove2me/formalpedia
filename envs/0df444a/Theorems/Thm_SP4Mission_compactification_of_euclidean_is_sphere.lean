-- Prove2me | Theorems.Thm_SP4Mission_compactification_of_euclidean_is_sphere
-- name    : SP4Mission.compactification_of_euclidean_is_sphere
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T14:21:20.998698+00:00
-- url     : https://prove2.me/theorems/2dda19d1-2376-47ba-a220-01da18193dd6
-- title:
--   Compactification of Euclidean space is the sphere
-- statement:
--   Let $M$ be a compact Hausdorff topological 4-manifold. If there exists a point $p \in M$ such that the punctured space $M \setminus \{p\}$ is homeomorphic to $\mathbb{R}^4$, then $M$ itself is homeomorphic to the standard 4-sphere $S^4$. This is a purely point-set topological fact following from the fact that a compact Hausdorff space is canonically the Alexandroff one-point compactification of the complement of any point, and the one-point compactification of $\mathbb{R}^4$ is $S^4$.
-- source:
--   General topology, Alexandroff one-point compactification.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.compactification_of_euclidean_is_sphere
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (p : M)
    (h : Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4))) :
    Nonempty (M ≃ₜ S4) := by sorry
