-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a1
-- name    : WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:23.693605+00:00
-- url     : https://prove2.me/theorems/cc6e681f-1c9c-4292-b225-453a51c0e59c
-- title:
--   Extract vertex and edge statistics of planar connected components
-- statement:
--   For a finite drawn graph, produce a finite list of connected-component vertex and edge counts that sums to the graph's total vertex and edge counts. Large components satisfy the assumed connected bound; components of size one or two satisfy the elementary small-component edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hconnected : ∀ {U : Type} [Fintype U] [LinearOrder U]
      (N : SimpleGraph U) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card U →
      N.edgeFinset.card ≤ 3 * Fintype.card U - 6)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) :
    ∃ parts : List (Nat × Nat),
      (parts.map Prod.fst).sum = Fintype.card V ∧
      (parts.map Prod.snd).sum = M.edgeFinset.card ∧
      ∀ p ∈ parts,
        (3 ≤ p.1 → p.2 ≤ 3 * p.1 - 6) ∧
        (p.1 < 3 → p.2 ≤ p.1) := by sorry
