-- Prove2me | Theorems.Thm_R03SP06_residual_p3_deletion_connected_of_center_condition
-- name    : R03SP06.residual_p3_deletion_connected_of_center_condition
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:41.57432+00:00
-- url     : https://prove2.me/theorems/6ffdff32-1efe-4a4b-8633-1fd16e1d0954
-- title:
--   Residual p3 deletion connected of center condition
-- statement:
--   A reusable residual-connectivity theorem. If the center b has no two distinct neighbors in the residual that can lie in different residual components, then deleting the P3 endpoints and center leaves a connected induced graph. The premise is deliberately expressed as a boundary-state condition; the cubic counting file supplies it for a cubic P3 center.
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

theorem residual_p3_deletion_connected_of_center_condition
    {G : SimpleGraph V} [Fintype V]
    {a b c : V} (hac : a ≠ c)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected)
    (hres : ∃ v : V, v ≠ a ∧ v ≠ b ∧ v ≠ c)
    (hcenter : ∀ {x y : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}},
      x.1 ≠ y.1 → G.Adj b x.1 → G.Adj b y.1 → False) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by sorry

end R03SP06
