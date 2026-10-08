-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_exists_circuit_iff_dependent
-- name    : WhitneyMatroid.RankCircuit.exists_circuit_iff_dependent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:26.182631+00:00
-- url     : https://prove2.me/theorems/7f4636bb-75fe-40a2-b54b-3479dc76fac7
-- title:
--   Theorem 4 — a circuit in N + e contains e iff e is dependent on N
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying $(\mathrm R_1)$–$(\mathrm R_3)$, let $N \subseteq M$ and let $e \notin N$. Then
--   $$\bigl(\exists \text{ a circuit } P \subseteq N + e \text{ with } e \in P\bigr) \iff r(N + e) = r(N).$$
--
--   This expresses dependence of an element on a set purely in terms of circuits, which is what makes the rank recoverable from the circuits (Theorem 5 and §8).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 512, Theorem 4

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem

namespace WhitneyMatroid.RankCircuit

theorem exists_circuit_iff_dependent {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) (N : Finset α) (e : α) (he : e ∉ N) :
    (∃ P : Finset α, circuitsOfRank r P ∧ P ⊆ insert e N ∧ e ∈ P) ↔ IsDependentOn r e N := by sorry

end WhitneyMatroid.RankCircuit
