-- Prove2me | Theorems.Thm_WilliamsonShmoys_bakerRoot_reachable
-- name    : WilliamsonShmoys.bakerRoot_reachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:24:17.700582+00:00
-- url     : https://prove2.me/theorems/c2eb9e7a-3681-4c1f-a7de-cc1359a3afe0
-- title:
--   A vertex is reachable from its canonical BFS root
-- statement:
--   The canonical root is selected from the vertices reachable from v, so it is connected to v. The parent concatenates this path with the lifted retained path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem WilliamsonShmoys.bakerRoot_reachable {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : G.Reachable (WilliamsonShmoys.bakerRoot G v) v := by sorry
