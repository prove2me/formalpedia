-- Prove2me | Theorems.Thm_SP4Mission_punctured_homotopy_sphere_weaklyContractible
-- name    : SP4Mission.punctured_homotopy_sphere_weaklyContractible
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T01:54:11.397361+00:00
-- url     : https://prove2.me/theorems/941a2dfc-2bc3-4f97-a11a-436be14bf72e
-- title:
--   A punctured homotopy four-sphere has trivial homotopy groups
-- statement:
--   Let $S^4$ be the unit sphere in $\mathbb R^5$. Let $M$ be a compact Hausdorff space (a type in universe zero) with a charted-space structure modeled on $\mathbb R^4$, so that $M$ is a closed topological $4$-manifold, and assume $M$ is homotopy equivalent to $S^4$. Then for every $p\in M$ the punctured manifold $M\setminus\{p\}$ is weakly contractible: it is nonempty and
--
--   $$
--   \pi_k\bigl(M\setminus\{p\},x\bigr)=0\qquad\text{for all } k\ge0 \text{ and all } x\in M\setminus\{p\}.
--   $$
--
--   This is the homotopy-group content of Freedman's remark "$\Sigma^4-\mathrm{pt}$ is contractible": the punctured homotopy sphere is path connected and simply connected, its positive-degree integral homology vanishes, and the Hurewicz theorem then kills all higher homotopy groups. Together with the Milnor–Whitehead theorem for manifolds it gives the contractibility of $M\setminus\{p\}$. No smooth structure is involved and no homeomorphism type is asserted.
--
--   **Formalization Note** The conclusion is `SP4WeakHomotopy.WeaklyContractible {x : M // x ≠ p}`; the hypothesis on $M$ is only a topological atlas, and the homotopy equivalence is `ContinuousMap.HomotopyEquiv M S4`.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136, proof of Theorem 1.6, p. 371: "Σ⁴ − pt is contractible so there is no obstruction to lifting the bundle"; proof of Theorem 1.5, p. 369 (the punctured manifolds M − pt are 1-connected). Classical route: Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem 1.20 (van Kampen) for simple connectivity, §2.1 (long exact sequence of a pair, p. 117) and Theorem 2.20 (excision) for the homology, Theorem 4.32 (Hurewicz), p. 366. Reduction child of SP4Mission.punctured_homotopy_sphere_contractible.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.punctured_homotopy_sphere_weaklyContractible
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    SP4WeakHomotopy.WeaklyContractible {x : M // x ≠ p} := by sorry
