-- Prove2me | Theorems.Thm_WhitneyMatroid_RankCircuit_nullity_eq_card_closesCircuit
-- name    : WhitneyMatroid.RankCircuit.nullity_eq_card_closesCircuit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:27:28.502515+00:00
-- url     : https://prove2.me/theorems/38c14c34-cd3b-4962-bf98-d6878a34302c
-- title:
--   Theorem 5 — the nullity counts the steps at which adding an element closes a circuit
-- statement:
--   Let $r$ be a rank function on the subsets of a finite set $M$ satisfying $(\mathrm R_1)$–$(\mathrm R_3)$, and let $N = e_1 + \cdots + e_p$ be built element by element from distinct elements $e_1, \dots, e_p$. Then
--   $$n(N) = \#\bigl\{\, i \in \{1,\dots,p\} : \text{there is a circuit of } r \text{ contained in } e_1 + \cdots + e_i \text{ that contains } e_i \,\bigr\}.$$
--
--   Whitney phrases this as: $n(N)$ is the number of times that adding an element increases the number of circuits present. It shows that the nullity, hence the rank, of a set is determined by the circuits it contains, and it is the model for the definition of rank from circuits in §8.
--
--   **Formalization Note** "Adding an element increases the number of circuits present" is rendered, following the paper's proof, as "there is a circuit in $e_1 + \cdots + e_i$ containing $e_i$": the circuits present in $e_1 + \cdots + e_i$ but not in $e_1 + \cdots + e_{i-1}$ are exactly those containing $e_i$. The ordered set $e_1, \dots, e_p$ is a duplicate-free list `l`; indices are 0-based in Lean. Nullity is integer valued.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 513, Theorem 5

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem
open Classical

namespace WhitneyMatroid.RankCircuit

theorem nullity_eq_card_closesCircuit {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) (l : List α) (hl : l.Nodup) :
    WhitneyMatroid.RankIndep.nullity r l.toFinset =
      ((Finset.univ : Finset (Fin l.length)).filter
        (fun i => ClosesCircuit (circuitsOfRank r) l i)).card := by sorry

end WhitneyMatroid.RankCircuit
