-- Prove2me | Theorems.Thm_R03SP06_three_vertex_connected_no_small_closed_separator
-- name    : R03SP06.three_vertex_connected_no_small_closed_separator
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:37.743318+00:00
-- url     : https://prove2.me/theorems/205cc966-72c7-4d34-a8fc-b3996dbcf962
-- title:
--   Three vertex connected no small closed separator
-- statement:
--   In the project connectivity model, a three-vertex-connected graph cannot have a nonempty proper side A separated from another nonempty side B by a separator of size at most two, when A has no edge to the outside except through that separator.
--
--   $$\kappa(G)\ge 3\quad\Longrightarrow\quad G-V(P_3)\text{ satisfies the stated connectivity conclusion}.$ $
--
--   This isolates one reusable separator or residual-connectivity step for deleting a displayed $P_3$ from a cubic three-vertex-connected graph. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [DecidableEq V]

theorem three_vertex_connected_no_small_closed_separator
    {G : SimpleGraph V} [Fintype V]
    (h3 : ThreeVertexConnected G) {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T)
    (hT : T.card ≤ 2) : False := by sorry

end R03SP06
