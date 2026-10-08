-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_rank_circuit_equivalence
-- name    : WhitneyMatroid.RankCircuit.rank_circuit_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:56.217304+00:00
-- url     : https://prove2.me/theorems/f11482e5-a575-4087-843c-ab5151fd0096
-- title:
--   §8 — the rank postulates (R) and the circuit postulates (C) are equivalent
-- statement:
--   Let $M$ be a finite set of elements. Whitney's rank postulates $(\mathrm R_1)$–$(\mathrm R_3)$ and circuit postulates $(\mathrm C_1)$, $(\mathrm C_2)$ define the same structures, through mutually inverse translations:
--
--   1. If $r$ satisfies $(\mathrm R_1)$–$(\mathrm R_3)$, then its circuits (minimal sets of positive nullity) satisfy $(\mathrm C_1)$, $(\mathrm C_2)$, the empty set is not a circuit, and the rank defined from these circuits is $r$ again:
--   $$r_{\mathcal C(r)} = r .$$
--   2. If a family $\mathcal C$ of nonempty subsets satisfies $(\mathrm C_1)$, $(\mathrm C_2)$, then the rank $r_{\mathcal C}$ defined from it satisfies $(\mathrm R_1)$–$(\mathrm R_3)$, and the circuits of $r_{\mathcal C}$ are exactly the members of $\mathcal C$:
--   $$\mathcal C(r_{\mathcal C}) = \mathcal C .$$
--
--   Here $\mathcal C(r)$ denotes the circuits of the rank function $r$, and $r_{\mathcal C}(N) = \sum_i \Gamma_i$ along an enumeration $e_1, \dots, e_p$ of $N$, with $\Gamma_i = 0$ if some member of $\mathcal C$ inside $\{e_1, \dots, e_i\}$ contains $e_i$ and $\Gamma_i = 1$ otherwise. In Whitney's words: the definitions of rank and of circuits under the two systems agree, and hence the systems are equivalent.
--
--   **Formalization Note** The paper takes the circuits to be nonempty tacitly: a circuit of a rank system has positive nullity, so it is never empty, while the family $\{\emptyset\}$ satisfies $(\mathrm C_1)$, $(\mathrm C_2)$ vacuously and its circuit rank has no circuits at all. The hypothesis "$\emptyset$ is not a circuit" is therefore added in part 2, and its counterpart is proved in part 1. The elements form a finite type, subsets are `Finset`s, ranks are integers, and the rank from circuits is computed along the enumeration `N.toList`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 517, §8 (last paragraph); with §5, p. 512, and §8, p. 516

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

namespace WhitneyMatroid.RankCircuit

theorem rank_circuit_equivalence (α : Type*) [Fintype α] [DecidableEq α] :
    (∀ r : Finset α → ℤ, IsRankSystem r →
      IsCircuitSystem (circuitsOfRank r) ∧ ¬ circuitsOfRank r ∅ ∧
        rankOfCircuits (circuitsOfRank r) = r) ∧
    (∀ C : Finset α → Prop, IsCircuitSystem C → ¬ C ∅ →
      IsRankSystem (rankOfCircuits C) ∧ circuitsOfRank (rankOfCircuits C) = C) := by sorry

end WhitneyMatroid.RankCircuit
