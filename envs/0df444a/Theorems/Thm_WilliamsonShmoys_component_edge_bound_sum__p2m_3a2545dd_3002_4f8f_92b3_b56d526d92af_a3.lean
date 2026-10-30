-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bound_sum__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
-- name    : WilliamsonShmoys.component_edge_bound_sum__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:06:50.581301+00:00
-- url     : https://prove2.me/theorems/3bd10af8-0975-451b-8419-6ac5ff23e627
-- title:
--   Sum planar edge bounds over connected components
-- statement:
--   If each component satisfies the sharp planar edge bound for size at least three and the complete-graph bound for smaller size, then the whole graph with at least three vertices satisfies 3n−6. The support `Fintype` is explicit to ensure the induced edge counts and cardinalities elaborate. This removes finite counting from the parent: component supports partition vertices, induced component edge sets account for the graph’s edges, and the small-component estimates retain sufficient slack. An independent proof route is finite partition counting followed by arithmetic, checking component sizes one and two separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_bound_sum__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hcomp : ∀ (c : G.ConnectedComponent) [Fintype c.supp],
      (G.induce c.supp).edgeSet.ncard <=
        if 3 <= Fintype.card c.supp then 3 * Fintype.card c.supp - 6
        else Fintype.card c.supp * (Fintype.card c.supp - 1) / 2) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
