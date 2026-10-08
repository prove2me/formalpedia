-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_exists_unique_strictFundamentalSet
-- name    : WhitneyMatroid.Binary.exists_unique_strictFundamentalSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:02:28.521512+00:00
-- url     : https://prove2.me/theorems/fe9a6ce8-0d86-4da3-9961-3a5cd825c4a1
-- title:
--   Theorem 9 — a base B = e₁ + ⋯ + e_{n−q} determines a unique strict fundamental set of circuits
-- statement:
--   Let $M$ be a matroid on the elements $e_1, \dots, e_n$, $n = r + q$, and suppose $B = \{e_1, \dots, e_{n-q}\}$ is a base of $M$. Then there is a strict fundamental set of circuits $P_1, \dots, P_q$ with respect to $e_{n-q+1}, \dots, e_n$, and it is unique:
--
--   $$\exists!\, (P_1, \dots, P_q) \text{ strict fundamental set of circuits of } M \text{ w.r.t. } e_{n-q+1}, \dots, e_n.$$
--
--   This is the matroid analogue of reducing a non-singular square submatrix to the unit matrix by row operations. It provides the fundamental circuits from which, for matroids satisfying (C\*), all cycles and circuits are recovered (Theorems 34 and 35) and the representing matrix is built (Theorem 37).
--
--   **Formalization Note** Elements are `Fin (r + q)` with $e_k \mapsto k-1$; the base is the range of `Fin.castAdd q`. The ground set of `M` is assumed to be all of `Fin (r + q)` (Whitney's matroid consists of exactly the elements $e_1, \dots, e_n$). Uniqueness is uniqueness of the whole indexed family $P_1, \dots, P_q$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 517, Theorem 9

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet

namespace WhitneyMatroid.Binary

/-- Theorem 9 (§9, p. 517). If `B = e₁ + ⋯ + e_{n-q}` is a base in `M = e₁ + ⋯ + eₙ`, then
there is a strict fundamental set of circuits with respect to `e_{n-q+1}, …, eₙ`; these circuits
are uniquely determined. Elements `e_k ↦ k - 1 : Fin (r + q)`, `n = r + q`. -/
theorem exists_unique_strictFundamentalSet {r q : ℕ} (M : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hB : M.IsBase (Set.range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∃! P : Fin q → Set (Fin (r + q)), IsStrictFundamentalSet M P := by sorry

end WhitneyMatroid.Binary
