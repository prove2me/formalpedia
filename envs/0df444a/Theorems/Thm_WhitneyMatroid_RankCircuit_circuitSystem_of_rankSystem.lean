-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_circuitSystem_of_rankSystem
-- name    : WhitneyMatroid.RankCircuit.circuitSystem_of_rankSystem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:39.174522+00:00
-- url     : https://prove2.me/theorems/1dbb6dc0-4faa-4a17-ae3b-6aa16d6804d9
-- title:
--   §5 — the circuits of a rank system satisfy (C₁) and (C₂)
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying $(\mathrm R_1)$–$(\mathrm R_3)$. Then its circuits (minimal sets of positive nullity) satisfy the circuit postulates:
--
--   1. $(\mathrm C_1)$ no proper subset of a circuit is a circuit;
--   2. $(\mathrm C_2)$ if $P_1, P_2$ are circuits, $e_1 \in P_1 \cap P_2$ and $e_2 \in P_1 \setminus P_2$, then there is a circuit $P_3 \subseteq P_1 \cup P_2$ with $e_2 \in P_3$ and $e_1 \notin P_3$.
--
--   This is the deduction of the circuit postulates from the rank postulates, one half of the equivalence of the two systems.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 512–513, §5 (Deduction of (C₁), (C₂) from (R₁), (R₂), (R₃))

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

namespace WhitneyMatroid.RankCircuit

theorem circuitSystem_of_rankSystem {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    IsCircuitSystem (circuitsOfRank r) := by sorry

end WhitneyMatroid.RankCircuit
