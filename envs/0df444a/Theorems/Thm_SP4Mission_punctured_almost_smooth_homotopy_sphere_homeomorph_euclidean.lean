-- Prove2me | Theorems.Thm_SP4Mission_punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean
-- name    : SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-08T04:10:15.637725+00:00
-- url     : https://prove2.me/theorems/3ce5dfc2-4002-4b0e-a39c-330f0b5cd9f7
-- title:
--   Freedman 1.5 (uniqueness, $\omega=0$) — a punctured almost-smooth homotopy four-sphere is homeomorphic to $\mathbb R^4$
-- statement:
--   This is the $h$-cobordism step in Freedman's proof of the topological four-dimensional Poincaré theorem: the uniqueness part of his classification theorem (Theorem 1.5) specialised to the zero intersection form, stated in the punctured form in which it is established in the source.
--
--   Let $S^4=\{x\in\mathbb R^5:\|x\|=1\}$. Let $M$ be a compact Hausdorff space (a type in universe zero) with a charted-space structure modeled on $\mathbb R^4$, so that $M$ is a closed topological $4$-manifold, and assume that $M$ is homotopy equivalent to $S^4$. Let $p\in M$, and suppose that the punctured manifold $M\setminus\{p\}$, with its subspace topology, has been given a smooth structure — an atlas modeled on $\mathbb R^4$ with $C^\infty$ transition maps — so that $M$ is an almost-smooth homotopy four-sphere in Freedman's sense. Then the punctured manifold is homeomorphic to Euclidean four-space:
--
--   $$
--   M\setminus\{p\}\;\cong_{\mathrm{Top}}\;\mathbb R^4 .
--   $$
--
--   Equivalently, $M\setminus\{p\}$ is homeomorphic to the punctured standard sphere $S^4\setminus\{\mathrm{pt}\}$. The conclusion is purely topological: the smooth structure on $M\setminus\{p\}$ enters only as a hypothesis, and no smoothness of the homeomorphism, no diffeomorphism $M\setminus\{p\}\cong\mathbb R^4$, and no uniqueness of smooth structures is asserted or implied. Combined with the smoothability of punctured homotopy four-spheres (`SP4Mission.punctured_homotopy_sphere_smoothable`) and with the fact that a compact Hausdorff space is the one-point compactification of the complement of any of its points, this statement gives Freedman's Theorem 1.6, $M\cong S^4$; in the source the corresponding sentence is that the homeomorphism $M-\mathrm{pt}\cong M'-\mathrm{pt}$ "extends to the 1-point compactification $M\cong M'$".
--
--   **Formalization Note** The smooth structure is carried by the instance hypotheses `ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p}` and `IsManifold (𝓡 4) ∞ {x : M // x ≠ p}`; the topology of the subtype is the subspace topology from $M$, so these charts are compatible with it. The conclusion is `Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4))`.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Theorem 1.5 (classification of closed almost-smooth 1-connected 4-manifolds), uniqueness part, in the case of the zero form ω = 0, which is realized by S⁴; its proof (pp. 370–371) produces a 5-dimensional proper h-cobordism (W; M′ − pt, M − pt) between the punctured manifolds, applies the proper h-cobordism theorem of Section 10 (Theorem 10.3; the proof of Theorem 1.5 invokes Theorem 10.4) to write (W; M′ − pt, M − pt) =_Top (M′ − pt) × [0,1], and concludes: "This gives a homeomorphism of M − pt to M′ − pt which extends to the 1-point compactification M ≅ M′." Proof of Theorem 1.6, p. 371: "This simply corresponds to the case ω = 0 of no intersection matrix." The present statement is the punctured homeomorphism M − pt ≅ S⁴ − pt ≅ ℝ⁴ obtained before the compactification step, with M′ = S⁴ and S⁴ − pt identified with ℝ⁴ by stereographic projection. Reduction child of SP4Mission.freedman_poincare_top (Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; milestone "Literature milestone: Topological four-dimensional Poincaré theorem").

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M)
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p}]
    [IsManifold (𝓡 4) ∞ {x : M // x ≠ p}] :
    Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4)) := by sorry
