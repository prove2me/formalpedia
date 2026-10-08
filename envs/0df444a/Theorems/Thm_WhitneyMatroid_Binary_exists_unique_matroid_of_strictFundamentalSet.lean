-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_exists_unique_matroid_of_strictFundamentalSet
-- name    : WhitneyMatroid.Binary.exists_unique_matroid_of_strictFundamentalSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:03:13.992684+00:00
-- url     : https://prove2.me/theorems/f342910c-23fe-47c8-a1a3-11ed0f902da8
-- title:
--   Theorem 36 — any admissible P₁, …, P_q is the strict fundamental set of a unique (C*)-matroid
-- statement:
--   Let $e_1, \dots, e_n$ be a set of elements, $n = r + q$, and let $P_1, \dots, P_q$ be any subsets such that $P_i$ contains $e_{n-q+i}$ and possibly elements from $e_1, \dots, e_{n-q}$ alone:
--
--   $$e_{n-q+i} \in P_i \subseteq \{e_1, \dots, e_{n-q}\} \cup \{e_{n-q+i}\} \qquad (i = 1, \dots, q).$$
--
--   Then there is a unique matroid $M$ on $e_1, \dots, e_n$ satisfying Postulate (C\*) with $P_1, \dots, P_q$ as a strict fundamental set of circuits (with respect to $e_{n-q+1}, \dots, e_n$).
--
--   In Whitney's words, this furnishes a simple method of constructing all matroids satisfying (C\*): each is obtained from a free choice of $q$ subsets of $e_1, \dots, e_{n-q}$.
--
--   **Formalization Note** Elements are `Fin (r + q)` ($e_k \mapsto k-1$); $e_{n-q+i}$ is `Fin.natAdd r (i-1)` and $\{e_1, \dots, e_{n-q}\}$ is the range of `Fin.castAdd q`. Uniqueness is among matroids whose ground set is all of `Fin (r + q)`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 531, Theorem 36

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet

namespace WhitneyMatroid.Binary

/-- Theorem 36 (Appendix, p. 531). Let `e₁, …, eₙ` (`Fin (r + q)`) be a set of elements, and let
`P₁, …, P_q` be any subsets such that `Pᵢ` contains `e_{n-q+i}` and possibly elements from
`e₁, …, e_{n-q}` alone. Then there is a unique matroid `M` on `e₁, …, eₙ` satisfying (C*), with
`P₁, …, P_q` as a strict fundamental set of circuits (with respect to `e_{n-q+1}, …, eₙ`). -/
theorem exists_unique_matroid_of_strictFundamentalSet {r q : ℕ}
    (P : Fin q → Set (Fin (r + q)))
    (hmem : ∀ i, Fin.natAdd r i ∈ P i)
    (hsub : ∀ i, P i ⊆ insert (Fin.natAdd r i) (Set.range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∃! M : Matroid (Fin (r + q)),
      M.E = Set.univ ∧ SatisfiesCStar {C | M.IsCircuit C} ∧ IsStrictFundamentalSet M P := by sorry

end WhitneyMatroid.Binary
