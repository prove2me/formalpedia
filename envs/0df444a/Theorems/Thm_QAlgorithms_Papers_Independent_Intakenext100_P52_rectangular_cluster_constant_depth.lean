-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_rectangular_cluster_constant_depth
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.rectangular_cluster_constant_depth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:38:29.507722+00:00
-- url     : https://prove2.me/theorems/397f7678-8578-40c5-a4b8-b6a4af5aa63f
-- title:
--   §5: constant-depth cluster preparation
-- statement:
--   For a rectangular $r\times c$ grid, including a one-dimensional row, let $|C_{r,c}\rangle$ be the state obtained by preparing $|+\rangle$ at every vertex and applying $CZ$ once on every horizontal and vertical nearest-neighbour edge. There is a natural constant $D\le5$, independent of both grid dimensions, such that
--
--   $$ \forall r,c\quad\exists\text{ a preparation of }|C_{r,c}\rangle\text{ of depth at most }D. $$
--
--   Every physical layer consists of gates on pairwise disjoint supports, and all two-qubit gates are nearest-neighbour $CZ$s. Four edge matchings and the initial Hadamard layer give a bound uniform in grid size. Empty grids have the scalar vacuum state.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 8, §5: constant-depth cluster preparation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Cluster preparation, PDF p.8: a dimension-independent constant comes before
both grid dimensions. Four disjoint CZ matchings plus one H layer suffice;
commutation is not treated as permission to overlap gates in a physical layer. -/
theorem rectangular_cluster_constant_depth :
    ∃ D : ℕ, D ≤ 5 ∧ ∀ r c : ℕ,
      ∃ layers : List (List (PrepGate (RectangularSites r c))),
        layers.length ≤ D ∧ (∀ L ∈ layers, LegalPrepLayer L) ∧
        (∀ g ∈ layers.flatten, GridPrepGate g) ∧
        act (prepMatrix layers) (ket (fun _ : RectangularSites r c => false)) = graphClusterState (gridEdges r c) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
