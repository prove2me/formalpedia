-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_rankSeq_swap_last
-- name    : WhitneyMatroid.RankCircuit.rankSeq_swap_last
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:26:49.10627+00:00
-- url     : https://prove2.me/theorems/ac736ba3-62de-411f-a83b-77ae8632a9c0
-- title:
--   Lemma 7 — interchanging the last two elements does not change the circuit rank
-- statement:
--   Let the subsets of a finite set $M$ be divided into circuits and non-circuits so that $(\mathrm C_1)$ and $(\mathrm C_2)$ hold, and let $r(e_1, \dots, e_q) = \sum_i \Gamma_i$ be the rank of an ordered list defined from circuits ($\Gamma_i = 0$ if some circuit inside $\{e_1, \dots, e_i\}$ contains $e_i$, else $\Gamma_i = 1$). For distinct elements $e_1, \dots, e_q$,
--   $$r(e_1, \dots, e_{q-2}, e_{q-1}, e_q) = r(e_1, \dots, e_{q-2}, e_q, e_{q-1}).$$
--
--   This is the key step toward Lemma 8, that the circuit rank of a set does not depend on how its elements are ordered.
--
--   **Formalization Note** The list $(e_1,\dots,e_{q-2})$ is `l`, and $e_{q-1}, e_q$ are `a`, `b`; the whole list `l ++ [a, b]` is required to have no repetitions, as the paper's "ordered set of elements" implies.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 516, Lemma 7

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

namespace WhitneyMatroid.RankCircuit

theorem rankSeq_swap_last {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α → Prop) (hC : IsCircuitSystem C) (l : List α) (a b : α)
    (hnd : (l ++ [a, b]).Nodup) :
    rankSeq C (l ++ [a, b]) = rankSeq C (l ++ [b, a]) := by sorry

end WhitneyMatroid.RankCircuit
