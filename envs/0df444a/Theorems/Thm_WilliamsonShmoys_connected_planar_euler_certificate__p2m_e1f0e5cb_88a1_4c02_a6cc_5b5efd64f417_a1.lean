-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1
-- name    : WilliamsonShmoys.connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:32.095231+00:00
-- url     : https://prove2.me/theorems/2c120eb1-ceed-4c13-9974-ca3513a96318
-- title:
--   Euler and face-boundary certificate for a connected plane graph
-- statement:
--   There is a natural number of faces F for which the connected drawn simple graph satisfies the plane Euler equation |V| + F = |E| + 2 and the total face-boundary incidence bound 3F ≤ 2|E|. The vertex lower bound and simplicity ensure every face boundary walk has length at least three; each edge contributes two incidences, including bridges. A proof route is to construct a finite plane map from the supplied arcs, apply Euler’s formula, and count face-side incidences. This isolates the remaining topological construction and counting argument; it does not claim that obligation is already proved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) : ∃ F : ℕ, (3 * F <= 2 * H.edgeSet.ncard) ∧ (Fintype.card V + F = H.edgeSet.ncard + 2) := by sorry
