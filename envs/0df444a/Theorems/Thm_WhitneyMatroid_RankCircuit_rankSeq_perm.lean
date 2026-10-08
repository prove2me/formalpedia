-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_rankSeq_perm
-- name    : WhitneyMatroid.RankCircuit.rankSeq_perm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:26:49.263648+00:00
-- url     : https://prove2.me/theorems/745eef48-c165-4144-982c-94959171a138
-- title:
--   Lemma 8 — the circuit rank of a set is independent of the ordering of its elements
-- statement:
--   Let the subsets of a finite set $M$ be divided into circuits and non-circuits so that $(\mathrm C_1)$ and $(\mathrm C_2)$ hold, and let $r(e_1, \dots, e_p) = \sum_i \Gamma_i$ be the rank of an ordered list defined from circuits. If $(e_1, \dots, e_p)$ has no repetitions and $(f_1, \dots, f_p)$ is a reordering of it, then
--   $$r(e_1, \dots, e_p) = r(f_1, \dots, f_p).$$
--
--   Hence the rank of a subset defined from circuits is well defined, independent of the chosen enumeration of its elements.
--
--   **Formalization Note** Orderings of the elements of $N$ are duplicate-free lists; "reordering" is `List.Perm`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 517, Lemma 8

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

namespace WhitneyMatroid.RankCircuit

theorem rankSeq_perm {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α → Prop) (hC : IsCircuitSystem C) (l₁ l₂ : List α) (hnd : l₁.Nodup)
    (hperm : l₁.Perm l₂) :
    rankSeq C l₁ = rankSeq C l₂ := by sorry

end WhitneyMatroid.RankCircuit
