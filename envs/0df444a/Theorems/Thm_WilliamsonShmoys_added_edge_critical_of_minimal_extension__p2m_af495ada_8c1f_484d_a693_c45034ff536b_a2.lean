-- Prove2me | Theorems.Thm_WilliamsonShmoys_added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- name    : WilliamsonShmoys.added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:07.311816+00:00
-- url     : https://prove2.me/theorems/564c7d1b-b3fd-403f-9f4d-18453c2c2050
-- title:
--   Every added edge of a minimal connected extension is critical
-- statement:
--   For a connected extension minimal under inclusion, deleting any edge outside M disconnects its endpoints. An alternate route would preserve connectedness and M after deletion, contradicting minimality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H) (hconn : H.Connected)
    (hmin : ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → K = H) :
    ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
      ¬ (H.deleteEdges {s(u, v)}).Reachable u v := by sorry
