-- Prove2me | Theorems.Thm_SP4Mission_punctured_homotopy_sphere_homology_zero
-- name    : SP4Mission.punctured_homotopy_sphere_homology_zero
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T01:54:27.198828+00:00
-- url     : https://prove2.me/theorems/54d5ef69-987f-4647-a62b-21cc6cedaea7
-- title:
--   $H_k(\Sigma^4\setminus\{p\};\mathbb Z)=0$ for $k\ge1$: a punctured homotopy four-sphere is acyclic
-- statement:
--   Let $S^4$ be the unit sphere in $\mathbb R^5$. Let $M$ be a compact Hausdorff space (a type in universe zero) with a charted-space structure modeled on $\mathbb R^4$, so that $M$ is a closed topological $4$-manifold, and assume $M$ is homotopy equivalent to $S^4$. Then for every $p\in M$ and every $k\ge1$,
--
--   $$
--   H_k\bigl(M\setminus\{p\};\mathbb Z\bigr)=0 .
--   $$
--
--   The computation is the long exact sequence of the pair $(M, M\setminus\{p\})$: by homotopy invariance $H_k(M)\cong H_k(S^4)$, which is $\mathbb Z$ for $k=4$ and $0$ for $k\ge1$, $k\ne4$; by excision $H_k(M,M\setminus\{p\})\cong H_k(B,B\setminus\{p\})$ for a coordinate ball $B$, which is $\mathbb Z$ for $k=4$ and $0$ otherwise; and for the closed connected orientable $4$-manifold $M$ the map $H_4(M)\to H_4(M,M\setminus\{p\})$ is the isomorphism carrying the fundamental class to a local generator. Exactness then gives the vanishing in every positive degree. Together with simple connectivity and the Hurewicz theorem this yields the weak contractibility of the punctured homotopy sphere.
--
--   **Formalization Note** `SP4Homology.H k X` is Mathlib's integral singular homology; vanishing is `IsZero`. The hypothesis on $M$ is only a topological atlas, and the homotopy equivalence is `ContinuousMap.HomotopyEquiv M S4`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf): long exact sequence of the pair (X, A) in singular homology, §2.1, p. 117 (following Theorem 2.16); Corollary 2.11, p. 111 (homotopy invariance); Corollary 2.14, p. 114 (homology of spheres); Theorem 2.20, p. 119 (excision); Theorem 3.26(a), p. 236 (for a closed connected R-orientable n-manifold the map Hₙ(M; R) → Hₙ(M | x; R) ≅ R is an isomorphism). Statement in the source: Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136, proof of Theorem 1.6, p. 371 ("Σ⁴ − pt is contractible"). Reduction child of SP4Mission.punctured_homotopy_sphere_weaklyContractible.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.punctured_homotopy_sphere_homology_zero
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) (k : ℕ) (hk : 1 ≤ k) :
    IsZero (SP4Homology.H k {x : M // x ≠ p}) := by sorry
