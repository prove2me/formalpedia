-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- name    : WilliamsonShmoys.component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:05.684837+00:00
-- url     : https://prove2.me/theorems/dce49140-44b6-4a2b-8434-7024437468bf
-- title:
--   Partition edges across a disconnected reachable component
-- statement:
--   For unreachable vertices u and v, construct the reachable component S of u and two spanning graphs whose edges partition G's edges, with one graph supported on S and the other on its complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ S : Set V, ∃ A B : SimpleGraph V,
      u ∈ S ∧ v ∉ S ∧
      (∀ a b, G.Adj a b ↔ A.Adj a b ∨ B.Adj a b) ∧
      (∀ a b, A.Adj a b → a ∈ S ∧ b ∈ S) ∧
      (∀ a b, B.Adj a b → a ∉ S ∧ b ∉ S) := by sorry
