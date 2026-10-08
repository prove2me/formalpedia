-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_matrix_matroid_satisfies_cStar
-- name    : WhitneyMatroid.Binary.matrix_matroid_satisfies_cStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:03:52.775422+00:00
-- url     : https://prove2.me/theorems/ce293e24-a6c8-422d-8ce9-9e42eefea8bb
-- title:
--   Appendix, p. 532 — the matroid of a matrix mod 2 satisfies (C*), and the two notions of cycle agree
-- statement:
--   Let $\mathbf M$ be an $m \times n$ matrix of integers mod 2 with columns $C_1, \dots, C_n$, and let $M$ be the set of elements $e_1, \dots, e_n$ corresponding to the columns, a set of elements being independent (equivalently, a circuit) in $M$ exactly when the corresponding columns are independent (a circuit) mod 2. Then:
--
--   1. $M$ is a matroid;
--   2. $M$ satisfies Postulate (C\*);
--   3. the definitions of cycle in $M$ and in $\mathbf M$ agree: a set $Q$ of elements is a cycle of $M$ (a sum mod 2 of circuits) if and only if there are coefficients $\alpha_1, \dots, \alpha_n$ (integers mod 2) with
--
--   $$\alpha_1 C_1 + \dots + \alpha_n C_n \equiv 0 \pmod 2 \quad\text{and}\quad Q = \{ e_j : \alpha_j \not\equiv 0 \}.$$
--
--   This is the easy direction of Whitney's characterization: every matroid of a matrix mod 2 satisfies (C\*). Theorem 37 is the converse.
--
--   **Formalization Note** Item 1 is the existence of a Mathlib matroid `M` on `Fin n` with `IsMatroidOf M A`; items 2 and 3 are asserted for every such `M` (there is only one). The linear combination is `A.mulVec x = 0` for `x : Fin n → ZMod 2`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 532, Appendix (unnumbered: 'We shall show that M is a matroid satisfying (C*) and the definitions of cycle in M and 𝐌 agree')

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsMatroidOf

namespace WhitneyMatroid.Binary

/-- Appendix, p. 532. Let `A` be an `m × n` matrix of integers mod 2 with columns `C₁, …, Cₙ`,
and let `M` be the set of elements `e₁, …, eₙ` (`Fin n`) corresponding to the columns, with the
independent (equivalently, circuit) sets of the columns as its independent (circuit) sets. Then
`M` is a matroid satisfying (C*), and the definitions of cycle in `M` and in `A` agree: a set `Q`
of elements is a cycle of `M` (a sum mod 2 of circuits) iff `Q` is the set of columns with
coefficient `1` in a linear combination `Σ αᵢ Cᵢ ≡ 0 (mod 2)`. -/
theorem matrix_matroid_satisfies_cStar {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∃ M : Matroid (Fin n), IsMatroidOf M A) ∧
      ∀ M : Matroid (Fin n), IsMatroidOf M A →
        SatisfiesCStar {C | M.IsCircuit C} ∧
          ∀ Q : Set (Fin n), IsCycleOf {C | M.IsCircuit C} Q ↔
            ∃ x : Fin n → ZMod 2, A.mulVec x = 0 ∧ Q = {j | x j ≠ 0} := by sorry

end WhitneyMatroid.Binary
