-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_circuit_of_minimal_dependent
-- name    : WhitneyMatroid.RankCircuit.circuit_of_minimal_dependent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:39.350659+00:00
-- url     : https://prove2.me/theorems/90316cba-ebb0-4d61-a7c9-2590f5f1d65a
-- title:
--   Lemma 6 — if e is dependent on P₁ but on no proper subset of P₁, then P₁ + e is a circuit
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying $(\mathrm R_1)$–$(\mathrm R_3)$. Let $P_1 \subseteq M$ and $e \notin P_1$. Suppose $e$ is dependent on $P_1$, i.e. $r(P_1 + e) = r(P_1)$, but on no proper subset of $P_1$: $r(Q + e) \ne r(Q)$ for every $Q \subset P_1$, $Q \neq P_1$. Then
--   $$P = P_1 + e \ \text{ is a circuit of } r.$$
--
--   Together with Lemma 5 this is the bridge between dependence of an element on a set and circuits through that element (Theorem 4).
--
--   **Formalization Note** The hypothesis $e \notin P_1$ is tacit in the paper (it writes $P = P_1 + e$ and its proof uses $\rho(P_1) < \rho(P)$); it is added as a binder.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 512, Lemma 6

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem

namespace WhitneyMatroid.RankCircuit

theorem circuit_of_minimal_dependent {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) (P₁ : Finset α) (e : α) (he : e ∉ P₁)
    (hdep : IsDependentOn r e P₁) (hmin : ∀ Q : Finset α, Q ⊂ P₁ → ¬ IsDependentOn r e Q) :
    circuitsOfRank r (insert e P₁) := by sorry

end WhitneyMatroid.RankCircuit
