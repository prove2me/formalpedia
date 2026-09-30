-- Prove2me | Theorems.Thm_SP4Mission_punctured_homotopy_sphere_smoothable
-- name    : SP4Mission.punctured_homotopy_sphere_smoothable
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-08T04:10:10.870368+00:00
-- url     : https://prove2.me/theorems/775fc2e6-b508-4f1b-8662-b69611308b9e
-- title:
--   Freedman 1.6, smoothing step — a punctured homotopy four-sphere is almost smooth
-- statement:
--   This is the smoothing step in Freedman's proof of the topological four-dimensional Poincaré theorem: a homotopy four-sphere is an *almost-smooth* manifold in Freedman's sense, that is, it carries a smooth structure in the complement of a single point.
--
--   Let $S^4=\{x\in\mathbb R^5:\|x\|=1\}$ be the standard four-sphere. Let $M$ be a compact Hausdorff space (a type in universe zero) equipped with a charted-space structure modeled on $\mathbb R^4$, so that $M$ is a closed topological $4$-manifold, and assume that $M$ is homotopy equivalent to $S^4$. Then for every point $p\in M$ the punctured manifold $M\setminus\{p\}$, with its subspace topology, admits a smooth structure: there is an atlas of charts of $M\setminus\{p\}$ modeled on $\mathbb R^4$ whose transition maps are $C^\infty$. Symbolically,
--
--   $$
--   M\simeq S^4\quad\Longrightarrow\quad \forall\,p\in M:\ \ M\setminus\{p\}\ \text{admits a } C^\infty \text{ structure}.
--   $$
--
--   The statement asserts the existence of some smooth structure compatible with the given topology of $M\setminus\{p\}$. It makes no claim about uniqueness of that structure, about smoothness at $p$, or about any relation between this structure and a homeomorphism to $S^4$, and it does not by itself imply that $M$ is homeomorphic to $S^4$. Together with the punctured uniqueness statement `SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean` and one-point compactification, it yields Freedman's Theorem 1.6; the same smoothability holds for every connected topological $4$-manifold (Quinn), but only the homotopy-sphere case is stated here, exactly as used in the source.
--
--   **Formalization Note** The smooth structure is expressed as the existence of a `ChartedSpace (EuclideanSpace ℝ (Fin 4))` instance on the subtype $\{x : M \mid x \ne p\}$ together with `IsManifold (𝓡 4) ∞` for that instance. The topology of the subtype is the subspace topology inherited from $M$, so the charts are automatically compatible with it. The hypothesis on $M$ is only a topological charted-space structure; no differentiability is assumed on $M$.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Proof of Theorem 1.6 (the 4-dimensional Poincaré conjecture), p. 371: "It remains only to see that any possible Σ⁴ will be an almost smooth manifold. Σ⁴ − pt is contractible so there is no obstruction to lifting the bundle. Apply smoothing theory for noncompact manifolds to smooth Σ⁴ − pt." Section 1, definition preceding Theorem 1.5: "A manifold is almost-smooth if it has been given a smooth structure in the complement of a single point." General smoothing input: Frank Quinn, Ends of maps. III: Dimensions 4 and 5, J. Differential Geom. 17 (1982), 503–521, Corollary 2.2.3, p. 507 (any 4-manifold has a smooth structure in the complement of a point). Reduction child of SP4Mission.freedman_poincare_top (Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; milestone "Literature milestone: Topological four-dimensional Poincaré theorem").

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.punctured_homotopy_sphere_smoothable
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p},
      IsManifold (𝓡 4) ∞ {x : M // x ≠ p} := by sorry
