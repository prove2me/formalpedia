-- Prove2me | Theorems.Thm_SP4Mission_manifold_homotopyEquiv_cwComplex
-- name    : SP4Mission.manifold_homotopyEquiv_cwComplex
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T02:57:33.477299+00:00
-- url     : https://prove2.me/theorems/581cb122-47cf-4f4c-9e46-59ce3d946a11
-- title:
--   Milnor: a separable topological manifold has the homotopy type of a countable CW complex
-- statement:
--   Let $X$ be a Hausdorff, second countable topological space with a charted-space structure modelled on $\mathbb R^n$, i.e. a separable metrizable topological $n$-manifold (without boundary, $n\ge0$ arbitrary). Then there is a Hausdorff space $Y$ carrying the structure of a CW complex with countably many cells in each dimension, together with a homotopy equivalence
--
--   $$
--   X\;\simeq\;Y .
--   $$
--
--   This is Milnor's theorem that a separable metric ANR — in particular any separable topological manifold — has the homotopy type of a countable CW complex (Milnor 1959, Corollary 1 to Theorem 1; the manifold case is stated explicitly there). It is the bridge that makes Whitehead's theorem available for manifolds: homotopy-theoretic statements about CW complexes (such as "weakly contractible implies contractible") transfer to manifolds along this homotopy equivalence. Second countability is essential: the long line is a Hausdorff $1$-manifold which is not of the homotopy type of any CW complex.
--
--   **Formalization Note** The manifold hypothesis is `ChartedSpace (EuclideanSpace ℝ (Fin n)) X` with `T2Space X` and `SecondCountableTopology X`; no smooth structure is involved. The CW complex is Mathlib's `Topology.CWComplex (Set.univ : Set Y)` (Whitehead's classical definition, on the whole space $Y$), with `T2Space Y` required separately since Mathlib's class does not include the Hausdorff condition, and countability is `∀ m, Countable (h.cell m)` for the cell-index types of the structure `h`. The homotopy equivalence is `ContinuousMap.HomotopyEquiv X Y`, and $Y$ is taken in the same universe as $X$.
-- source:
--   John Milnor, On spaces having the homotopy type of a CW-complex, Trans. Amer. Math. Soc. 90 (1959), 272–280, https://www.ams.org/journals/tran/1959-090-02/S0002-9947-1959-0100267-4/, Theorem 1, p. 272 (the class W₀ of spaces having the homotopy type of a countable CW-complex coincides with the spaces dominated by a countable CW-complex, the spaces of the homotopy type of a countable locally finite simplicial complex, and the spaces of the homotopy type of an absolute neighborhood retract) and Corollary 1, p. 272: "Every separable manifold belongs to the class W₀." See also S. Friedl, M. Nagel, P. Orson, M. Powell, The foundations of four-manifold theory in the topological category, NYJM Monographs 6 (2025), Theorem 3.16 and the proof on pp. 23–24 (every manifold is an ANR, after Hanner).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.manifold_homotopyEquiv_cwComplex.{u}
    (n : ℕ) (X : Type u) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (h : Topology.CWComplex (Set.univ : Set Y)),
      T2Space Y ∧ (∀ m : ℕ, Countable (h.cell m)) ∧
        Nonempty (ContinuousMap.HomotopyEquiv X Y) := by sorry
