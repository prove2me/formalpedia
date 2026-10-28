-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_edge_bound
-- name    : WilliamsonShmoys.connected_component_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:49:08.745124+00:00
-- url     : https://prove2.me/theorems/fb8ac739-3d59-4ce5-9b11-df3dc591146c
-- title:
--   Connected component edge bound by size
-- statement:
--   For a nonempty connected induced subgraph, use the assumed bound when its vertex set has size at least three. For size one or two, simplicity of the graph bounds the edge count by the size minus one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (C : Set V) [Fintype C]
    (hC : C.Nonempty)
    (hconnected : (K.induce C).Connected)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    (K.induce C).edgeSet.ncard ≤
      (if C.ncard < 3 then C.ncard - 1 else 3 * C.ncard - 6) := by sorry
