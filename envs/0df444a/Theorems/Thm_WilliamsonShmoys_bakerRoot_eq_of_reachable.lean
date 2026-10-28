-- Prove2me | Theorems.Thm_WilliamsonShmoys_bakerRoot_eq_of_reachable
-- name    : WilliamsonShmoys.bakerRoot_eq_of_reachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:23:43.244999+00:00
-- url     : https://prove2.me/theorems/85cfcdc6-8dbf-424a-830b-e15fbf937bae
-- title:
--   Canonical BFS roots agree on a connected component
-- statement:
--   Reachable vertices have the same least-labelled reachable vertex, hence the same canonical BFS root. The parent uses this to rewrite the retained-level bounds as distances from v's root.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem WilliamsonShmoys.bakerRoot_eq_of_reachable {n : Nat} (G : SimpleGraph (Fin n)) {u v : Fin n} (h : G.Reachable u v) : WilliamsonShmoys.bakerRoot G u = WilliamsonShmoys.bakerRoot G v := by sorry
