-- Prove2me | Theorems.Thm_Transcendence_exists_int_pow_repr
-- name    : Transcendence.exists_int_pow_repr
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:43:55.474687+00:00
-- url     : https://prove2.me/theorems/08874ba9-1330-4e88-94e4-bb411e88f3b6
-- title:
--   Scaled powers of an algebraic number are integer combinations of a fixed basis, with geometrically growing coefficients
-- statement:
--   Let $K$ be a field of characteristic zero and $\alpha \in K$ algebraic over $\mathbb{Q}$. There are $\ell, A \in \mathbb{N}$ and an integer $L \neq 0$ such that for every $n$,
--
--   $$L^{n}\alpha^{n} = \sum_{l < \ell} r_l\, \alpha^{l}$$
--
--   for some integers $r_l$ with $|r_l| \le A^{n}$.
--
--   Take for $L$ the leading coefficient of an integer polynomial vanishing at $\alpha$: then $L\alpha$ is an algebraic integer, and reducing its powers modulo a monic integer polynomial keeps the coefficients geometrically bounded.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- Integral representations of the powers of an algebraic number, with controlled coefficients.

Let `α` be algebraic over `ℚ` in a field of characteristic zero, and let `m ∈ ℤ[X]` be a
non-constant integer polynomial vanishing at `α`, of degree `ℓ` and leading coefficient `L`.
Reducing `(L X)ⁿ` modulo `m` expresses `Lⁿ αⁿ` in the basis `1, α, …, α^(ℓ-1)` with integer
coordinates, and each reduction step multiplies the size of the coordinates by at most
`|L| + (sum of the absolute values of the coefficients of m)`. So the coordinates of `Lⁿ αⁿ`
are at most `Aⁿ` in absolute value, for a constant `A` depending only on `α`. -/
theorem exists_int_pow_repr {K : Type*} [Field K] [CharZero K] {α : K} (hα : IsAlgebraic ℚ α) :
    ∃ (ℓ A : ℕ) (L : ℤ), L ≠ 0 ∧ ∀ n : ℕ, ∃ r : ℕ → ℤ,
      (L : K) ^ n * α ^ n = ∑ l ∈ Finset.range ℓ, (r l : K) * α ^ l ∧
        ∀ l, (r l).natAbs ≤ A ^ n := by
  sorry

end Transcendence
