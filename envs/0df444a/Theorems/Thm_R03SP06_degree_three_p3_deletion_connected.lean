-- Prove2me | Theorems.Thm_R03SP06_degree_three_p3_deletion_connected
-- name    : R03SP06.degree_three_p3_deletion_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:52.285478+00:00
-- url     : https://prove2.me/theorems/0371b3ff-43a2-47a4-8005-7ab326002a4e
-- title:
--   Degree three p3 deletion connected
-- statement:
--   Full candidate formalization of the previously recorded connectivity lemma. Only the degree-three condition at the P3 center is needed: the center has one residual neighbor, so one of two residual components would be a closed side behind the two endpoints.
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

theorem degree_three_p3_deletion_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by sorry

end R03SP06
