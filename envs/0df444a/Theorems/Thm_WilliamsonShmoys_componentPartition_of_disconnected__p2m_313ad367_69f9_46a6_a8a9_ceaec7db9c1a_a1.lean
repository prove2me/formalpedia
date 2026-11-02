-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
-- name    : WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:55.577203+00:00
-- url     : https://prove2.me/theorems/ad9ec9d5-3963-45af-869f-03d998217399
-- title:
--   Finite connected-component vertex partition
-- statement:
--   For a finite graph that is disconnected and has at least three vertices, its connected components form a partition of the vertex type into at least two nonempty blocks, and each block induces a connected graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.componentPartition_of_disconnected__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a1
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
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) := by sorry
