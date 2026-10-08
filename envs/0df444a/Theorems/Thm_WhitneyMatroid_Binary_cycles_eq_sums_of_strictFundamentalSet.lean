-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_cycles_eq_sums_of_strictFundamentalSet
-- name    : WhitneyMatroid.Binary.cycles_eq_sums_of_strictFundamentalSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:03:03.720897+00:00
-- url     : https://prove2.me/theorems/57424662-c955-4a3a-b04c-802db2f8c118
-- title:
--   Theorem 34 — the cycles are the 2^q sums (mod 2) of a strict fundamental set
-- statement:
--   Let $M$ be a matroid on the elements $e_1, \dots, e_n$, $n = r + q$, satisfying Postulate (C\*), and let $P_1, \dots, P_q$ be a strict fundamental set of circuits in $M$ with respect to $e_{n-q+1}, \dots, e_n$. Then the cycles of $M$ are exactly the sums (mod 2) of subfamilies of $P_1, \dots, P_q$,
--
--   $$\{\text{cycles of } M\} = \Big\{ \textstyle\sum_{i \in s} P_i \ (\mathrm{mod}\ 2) \;:\; s \subseteq \{1, \dots, q\} \Big\},$$
--
--   and there are exactly $2^q$ cycles in $M$.
--
--   So the cycles of a (C\*)-matroid form a vector space over the integers mod 2 of dimension $q = n(M)$ with the fundamental circuits as a basis; this is the counting step behind Theorems 35 and 37.
--
--   **Formalization Note** Elements are `Fin (r + q)`, ground set all of it; subfamilies are indexed by `Finset (Fin q)` (with `P i` Whitney's $P_{i+1}$), and the number of cycles is the `Set.ncard` of the set of cycles.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 531, Theorem 34

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet

namespace WhitneyMatroid.Binary

/-- Theorem 34 (Appendix, p. 531). Let `M` be a matroid on `e₁, …, eₙ` (`Fin (r + q)`)
satisfying (C*), and let `P₁, …, P_q` be a strict fundamental set of circuits in `M` with respect
to `e_{n-q+1}, …, eₙ`. Then the cycles in `M` are exactly the sums (mod 2) of subfamilies of
`P₁, …, P_q`, and there are exactly `2^q` of them. -/
theorem cycles_eq_sums_of_strictFundamentalSet {r q : ℕ} (M : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hC : SatisfiesCStar {C | M.IsCircuit C})
    (P : Fin q → Set (Fin (r + q))) (hP : IsStrictFundamentalSet M P) :
    {Q | IsCycleOf {C | M.IsCircuit C} Q} = Set.range (fun s : Finset (Fin q) => sumMod2 s P) ∧
      {Q | IsCycleOf {C | M.IsCircuit C} Q}.ncard = 2 ^ q := by sorry

end WhitneyMatroid.Binary
