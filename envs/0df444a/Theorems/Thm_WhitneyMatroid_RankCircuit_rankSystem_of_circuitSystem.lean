-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_rankSystem_of_circuitSystem
-- name    : WhitneyMatroid.RankCircuit.rankSystem_of_circuitSystem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:47.813356+00:00
-- url     : https://prove2.me/theorems/4b4337b5-6f7d-47ac-874d-92dba8b701be
-- title:
--   §8 — the rank defined from circuits satisfies (R₁), (R₂), (R₃)
-- statement:
--   Let the subsets of a finite set $M$ be divided into circuits and non-circuits so that $(\mathrm C_1)$ and $(\mathrm C_2)$ hold, and let $r(N)$ be the rank of $N$ defined from circuits (the sum of the $\Gamma_i$ along an enumeration of $N$). Then $r$ satisfies the rank postulates:
--
--   1. $(\mathrm R_1)$ $r(\emptyset) = 0$;
--   2. $(\mathrm R_2)$ for $e \notin N$, $r(N + e) = r(N)$ or $r(N) + 1$;
--   3. $(\mathrm R_3)$ for $e_1, e_2 \notin N$, if $r(N + e_1) = r(N + e_2) = r(N)$, then $r(N + e_1 + e_2) = r(N)$.
--
--   This is the deduction of the rank postulates from the circuit postulates, the other half of the equivalence.
--
--   **Formalization Note** The rank of a set is computed along the fixed enumeration `N.toList`, so this statement holds only if the value is in effect independent of that choice (Lemma 8).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 516–517, §8

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

namespace WhitneyMatroid.RankCircuit

theorem rankSystem_of_circuitSystem {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α → Prop) (hC : IsCircuitSystem C) :
    IsRankSystem (rankOfCircuits C) := by sorry

end WhitneyMatroid.RankCircuit
