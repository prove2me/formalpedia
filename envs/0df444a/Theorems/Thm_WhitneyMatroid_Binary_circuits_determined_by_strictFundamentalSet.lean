-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_circuits_determined_by_strictFundamentalSet
-- name    : WhitneyMatroid.Binary.circuits_determined_by_strictFundamentalSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:03:08.422192+00:00
-- url     : https://prove2.me/theorems/06e2d209-7e3f-4d13-98d7-0d4059eb62ef
-- title:
--   Theorem 35 — the circuits of a strict fundamental set determine all circuits
-- statement:
--   As soon as the circuits of a strict fundamental set are known, all the circuits may be determined. Precisely: let $M$ and $M'$ be two matroids on the same elements $e_1, \dots, e_n$, $n = r + q$, both satisfying Postulate (C\*), and let $P_1, \dots, P_q$ be a strict fundamental set of circuits with respect to $e_{n-q+1}, \dots, e_n$ in both $M$ and $M'$. Then for every set $C$ of elements,
--
--   $$C \text{ is a circuit of } M \iff C \text{ is a circuit of } M'.$$
--
--   This contrasts with matroids in general: Whitney's example at the end of §9 gives two matroids with a common strict fundamental set and different circuits. Theorem 37 uses this result to identify the matroid of the constructed matrix with $M$.
--
--   **Formalization Note** Both matroids have ground set all of `Fin (r + q)`. "Determined" is formalized as the statement Theorem 37's proof uses: two (C\*)-matroids sharing a strict fundamental set have the same circuits.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 531, Theorem 35

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet

namespace WhitneyMatroid.Binary

/-- Theorem 35 (Appendix, p. 531). As soon as the circuits of a strict fundamental set are known,
all the circuits may be determined: two matroids `M`, `M'` on `e₁, …, eₙ` (`Fin (r + q)`), both
satisfying (C*), that have the same strict fundamental set of circuits `P₁, …, P_q` with respect
to `e_{n-q+1}, …, eₙ` have exactly the same circuits. -/
theorem circuits_determined_by_strictFundamentalSet {r q : ℕ} (M M' : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hE' : M'.E = Set.univ)
    (hC : SatisfiesCStar {C | M.IsCircuit C}) (hC' : SatisfiesCStar {C | M'.IsCircuit C})
    (P : Fin q → Set (Fin (r + q)))
    (hP : IsStrictFundamentalSet M P) (hP' : IsStrictFundamentalSet M' P) :
    ∀ C : Set (Fin (r + q)), M.IsCircuit C ↔ M'.IsCircuit C := by sorry

end WhitneyMatroid.Binary
