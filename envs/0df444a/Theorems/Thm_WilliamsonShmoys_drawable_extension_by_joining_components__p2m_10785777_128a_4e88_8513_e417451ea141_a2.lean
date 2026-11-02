-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
-- name    : WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:06.102438+00:00
-- url     : https://prove2.me/theorems/0dfd7289-30fc-4048-8084-2297688a9abc
-- title:
--   A disconnected drawable graph with enough vertices has a drawable extension joining distinct components
-- statement:
--   Every disconnected drawable graph on at least three vertices has a drawable proper supergraph formed by adding an edge between vertices that were in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ u v : V, ¬ M.Reachable u v ∧
      ∃ N : SimpleGraph V, M ≤ N ∧ N.Adj u v ∧
        HasPlanarDrawingOn N ∧ N ≠ M := by
  sorry
