-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_count_decreases_after_link
-- name    : WilliamsonShmoys.component_count_decreases_after_link
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:52:55.329218+00:00
-- url     : https://prove2.me/theorems/f5c13ea2-b667-439e-906c-17a0731b3395
-- title:
--   A link between components strictly decreases their number
-- statement:
--   If a graph is extended and the extension adds an edge between vertices that were not connected before, then the extension has strictly fewer connected components. The explicit finite instances make the cardinal comparison match the target’s binders.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.component_count_decreases_after_link
    {V : Type} [Fintype V]
    (Y Z : SimpleGraph V)
    (iY : Fintype Y.ConnectedComponent)
    (hYZ : Y ≤ Z)
    (u v : V)
    (hNotReachable : ¬ Y.Reachable u v)
    (hLink : Z.Adj u v) :
    ∃ (iZ : Fintype Z.ConnectedComponent),
      @Fintype.card Z.ConnectedComponent iZ <
        @Fintype.card Y.ConnectedComponent iY := by sorry
