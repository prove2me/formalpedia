-- Prove2me | Theorems.Thm_R03SP06_induced_not_connected_of_closed_side
-- name    : R03SP06.induced_not_connected_of_closed_side
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:06.050628+00:00
-- url     : https://prove2.me/theorems/9778ee41-b67c-454c-83b9-239deb21187a
-- title:
--   Induced not connected of closed side
-- statement:
--   A finite separator disconnects an induced graph when one nonempty side is closed under all edges except into the separator.
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

theorem induced_not_connected_of_closed_side
    {G : SimpleGraph V} {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T) :
    ¬ (G.induce {v : V | v ∉ T}).Connected := by sorry

end R03SP06
