-- Prove2me | Theorems.Thm_WilliamsonShmoys_bakerRoot_eq_of_min
-- name    : WilliamsonShmoys.bakerRoot_eq_of_min
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T16:02:53.284141+00:00
-- url     : https://prove2.me/theorems/024bbaf3-2e53-4ac5-81b5-9964ed55b453
-- title:
--   Recognising the Baker root of a component
-- statement:
--   Let $G$ be a graph on $\{0,\dots,n-1\}$ and let $r$ be a vertex such that no vertex $u<r$ can reach $r$. Then for every vertex $v$ reachable from $r$,
--
--   $$\operatorname{bakerRoot}_G(v)=r,$$
--
--   where $\operatorname{bakerRoot}_G(v)$ is the least label of a vertex in the connected component of $v$.
--
--   An algorithm that processes vertices in increasing order and starts a new breadth-first search from each vertex not yet visited therefore starts it exactly at the root used in the definition of `bakerLevel`, because all smaller vertices of the same component would already have been visited.
--
--   **Formalization Note.** `bakerRoot` is from `Def_WilliamsonShmoys_BakerLevel`.
-- source:
--   Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS started from one vertex per component)

import Mathlib
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false

theorem WilliamsonShmoys.bakerRoot_eq_of_min {n : ℕ} (G : SimpleGraph (Fin n)) (r v : Fin n) (hrv : G.Reachable r v)
    (hmin : ∀ u, u < r → ¬ G.Reachable u r) :
    WilliamsonShmoys.bakerRoot G v = r := by sorry
