-- Prove2me | Theorems.Thm_SP4Mission_punctured_homotopy_sphere_contractible
-- name    : SP4Mission.punctured_homotopy_sphere_contractible
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-08T05:08:56.254717+00:00
-- url     : https://prove2.me/theorems/d7bb3a1a-9b87-436d-a511-fd7808ff9079
-- title:
--   A punctured homotopy four-sphere is contractible
-- statement:
--   Let $S^4$ be the unit sphere in $\mathbb R^5$. Let $M$ be a compact Hausdorff space (a type in universe zero) with a charted-space structure modeled on $\mathbb R^4$, so that $M$ is a closed topological $4$-manifold, and assume that $M$ is homotopy equivalent to $S^4$. Then for every point $p\in M$ the punctured manifold $M\setminus\{p\}$, with its subspace topology, is contractible:
--
--   $$
--   M\simeq S^4\quad\Longrightarrow\quad M\setminus\{p\}\simeq\ast .
--   $$
--
--   This is the sentence "$\Sigma^4-\mathrm{pt}$ is contractible" in Freedman's proof of the four-dimensional Poincaré theorem. It supplies the contractibility hypothesis of the Stallings–Freedman characterization of $\mathbb R^4$ for the punctured homotopy sphere, and it is the reason the tangent microbundle of $\Sigma^4-\mathrm{pt}$ has no obstruction to a vector bundle reduction in the smoothing step. It is a statement of algebraic topology only: no smooth structure is involved and no homeomorphism type is asserted.
--
--   **Formalization Note** Contractibility is Mathlib's `ContractibleSpace {x : M // x ≠ p}`, the existence of a homotopy equivalence with a one-point space. The hypothesis on $M$ is only a topological atlas `ChartedSpace (EuclideanSpace ℝ (Fin 4)) M`; the homotopy equivalence is `ContinuousMap.HomotopyEquiv M S4`.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Proof of Theorem 1.6, p. 371: "Σ⁴ − pt is contractible so there is no obstruction to lifting the bundle." The same fact enters the proof of Corollary 1.2, p. 366 ("if the manifold in question is contractible there can be no obstruction to the lifting"), and the proof of Theorem 1.5, p. 369 ("(W; M′ − pt, M − pt) is a (topological) proper h-cobordism which is 1-connected"). Reduction child of SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.punctured_homotopy_sphere_contractible
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    ContractibleSpace {x : M // x ≠ p} := by sorry
