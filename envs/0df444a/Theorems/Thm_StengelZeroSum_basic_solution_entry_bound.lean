-- Prove2me | Theorems.Thm_StengelZeroSum_basic_solution_entry_bound
-- name    : StengelZeroSum.basic_solution_entry_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:39.09883+00:00
-- url     : https://prove2.me/theorems/ec905757-753b-4d7a-9a35-8a55cee17448
-- title:
--   Proof of Theorem 7(c) — Cramer bound $|x_j|\le\ell!\,\alpha^\ell$ on basic solutions
-- statement:
--   Let $G$ be an integer matrix with $\ell$ rows and let $h$ be an integer vector, all of whose entries are at most $\alpha$ in absolute value. Then every basic solution $x$ of $Gx=h$ (the columns $G_j$ with $x_j\ne0$ linearly independent) satisfies
--
--   $$
--   |x_j|\le \ell!\,\alpha^\ell\qquad\text{for every } j .
--   $$
--
--   In the paper each basic variable is a quotient of two determinants whose denominator is at least $1$ in absolute value and whose numerator is at most $\ell!\,\alpha^\ell$; applied to the slack form of (58) with integral data, this gives the choice $M=\ell!\,\ell\,\alpha^\ell+1$.
--
--   **Formalization Note** $\ell$ is the number of rows; rows and columns are arbitrary finite types, and the system is read over $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the slack form of (58) for integral A, b, c (ℓ rows, entries from A, b, c or 0, 1, −1) → every integral system Gx = h with ℓ rows and entries of absolute value at most α; reason: the Cramer argument uses only integrality and the entry bound; the slack form of (58) is an instance once α ≥ 1
--   - encoding: each variable is the quotient of two determinants … numerator bounded by ℓ! α^ℓ → the resulting bound |x_j| ≤ ℓ! α^ℓ; reason: the bound on the quotient is what the proof of (c) uses
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, proof of Theorem 7(c), p.23

import Mathlib
import Definitions.Def_StengelZeroSum_IsBasic

open Matrix

namespace StengelZeroSum

/-- **Cramer bound on basic solutions of an integral system**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, proof of
Theorem 7(c), p.23: "Any basic solution is uniquely determined by the basis matrix, where each
variable is the quotient of two determinants where the denominator is at least 1 and the
numerator bounded in absolute value by ℓ! α^ℓ."

Let `G` be an integer matrix with `ℓ` rows and `h` an integer vector, all of whose entries are
at most `α` in absolute value. Every basic solution `x` of `Gx = h` (the columns `G_j` with
`x_j ≠ 0` linearly independent) satisfies `|x_j| ≤ ℓ! α^ℓ` for every `j`.

**Formalization Note** The page states this for the slack form of (58), which has `ℓ` rows and
entries from `A, b, c` or `0, 1, −1`; it is stated here for every integral system. Rows and
columns are arbitrary finite types, `ℓ` is the number of rows, and the system is read in `ℝ`
through the cast `ℤ → ℝ`. -/
theorem basic_solution_entry_bound {ρ κ : Type*} [Fintype ρ] [Fintype κ] (G : Matrix ρ κ ℤ)
    (h : ρ → ℤ) (α : ℕ) (hG : ∀ i j, |G i j| ≤ α) (hh : ∀ i, |h i| ≤ α) (x : κ → ℝ)
    (hx : G.map (Int.cast : ℤ → ℝ) *ᵥ x = fun i => (h i : ℝ))
    (hbasic : IsBasic (G.map (Int.cast : ℤ → ℝ)) x) :
    ∀ j, |x j| ≤ ((Fintype.card ρ).factorial : ℝ) * (α : ℝ) ^ Fintype.card ρ := by sorry

end StengelZeroSum
