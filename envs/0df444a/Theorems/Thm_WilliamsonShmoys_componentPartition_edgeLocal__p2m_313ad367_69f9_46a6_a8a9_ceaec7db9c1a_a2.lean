-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- name    : WilliamsonShmoys.componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:56.233012+00:00
-- url     : https://prove2.me/theorems/954faa17-a8ce-4e0c-b281-2379f22f5ab2
-- title:
--   Connected-component partition with edge locality
-- statement:
--   A finite disconnected graph with at least three vertices has at least two nonempty connected induced blocks forming a disjoint cover of all vertices, with block sizes summing to the vertex count; every edge has both endpoints in one block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.componentPartition_edgeLocal__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by sorry
