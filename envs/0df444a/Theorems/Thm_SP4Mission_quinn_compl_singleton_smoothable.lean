-- Prove2me | Theorems.Thm_SP4Mission_quinn_compl_singleton_smoothable
-- name    : SP4Mission.quinn_compl_singleton_smoothable
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-08T05:08:54.881105+00:00
-- url     : https://prove2.me/theorems/e18d319c-82d8-4133-95ec-c1498a4debef
-- title:
--   Quinn — a connected topological four-manifold has a smooth structure in the complement of a point
-- statement:
--   This is the smoothing theorem for open four-manifolds that underlies the "almost smooth" step in Freedman's work.
--
--   Let $N$ be a connected, Hausdorff, second countable topological space equipped with a charted-space structure modeled on $\mathbb R^4$, so that $N$ is a connected topological $4$-manifold without boundary, compact or not, and let $p\in N$. Then the punctured manifold $N\setminus\{p\}$, with its subspace topology, admits a smooth structure: an atlas modeled on $\mathbb R^4$ whose transition maps are $C^\infty$. In symbols,
--
--   $$
--   N\ \text{a connected topological 4-manifold},\ p\in N \quad\Longrightarrow\quad N\setminus\{p\}\ \text{admits a } C^\infty \text{ structure}.
--   $$
--
--   In Quinn's formulation, "any 4-manifold has a smooth structure in the complement of a point"; for a disconnected manifold one point must be removed from each compact component (Freedman–Quinn, Theorem 8.4), so connectedness is the implicit standing hypothesis, made explicit here. The theorem contains as special cases that every connected noncompact $4$-manifold is smoothable and that every closed connected $4$-manifold is almost smooth in Freedman's sense, with no hypothesis on the Kirby–Siebenmann invariant. Nothing is asserted about uniqueness of the smooth structure, about smoothness at $p$, or about extending the structure over $p$.
--
--   **Formalization Note** The conclusion is the existence of a `ChartedSpace (EuclideanSpace ℝ (Fin 4))` instance on the subtype `{x : N // x ≠ p}` together with `IsManifold (𝓡 4) ∞` for that instance; the subtype carries the subspace topology, so the smooth charts are automatically compatible with the topology of $N\setminus\{p\}$. The hypothesis `ChartedSpace (EuclideanSpace ℝ (Fin 4)) N` is only a topological atlas. Second countability is the usual standing convention for manifolds and excludes non-metrizable examples.
-- source:
--   Frank Quinn, Ends of maps. III: Dimensions 4 and 5, J. Differential Geom. 17 (1982), 503–521 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_Ends%20of%20maps%20III.pdf), Corollary 2.2.3, p. 507: "The map TOP(4)/O(4) → TOP/O is 3-connected. Consequently any 4-manifold has a smooth structure in the complement of a point, extending the canonical structure on the boundary"; also the introduction, p. 503. Michael H. Freedman and Frank Quinn, Topology of 4-Manifolds, Princeton Mathematical Series 39, Princeton University Press, 1990 (reformatted 2013 edition: https://archive.mpim-bonn.mpg.de/4789/2/FreedmanQuinn-TopologyOf4Manifolds-Reformatted2013.pdf), Section 8.3, Theorem 8.4, p. 121: "A 4-manifold has a smooth structure in the complement of any closed set with at least one point in each compact component. In particular a connected noncompact manifold is smoothable." Stated here for a connected manifold and a single point, the case used for Σ⁴ − pt in the proof of Freedman's Theorem 1.6 (Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf), p. 371). Reduction child of SP4Mission.punctured_homotopy_sphere_smoothable.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.quinn_compl_singleton_smoothable
    (N : Type*) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) N] (p : N) :
    ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : N // x ≠ p},
      IsManifold (𝓡 4) ∞ {x : N // x ≠ p} := by sorry
