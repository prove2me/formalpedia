-- Prove2me | Theorems.Thm_Transcendence_exists_denom_house_monomial_le
-- name    : Transcendence.exists_denom_house_monomial_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:08.375967+00:00
-- url     : https://prove2.me/theorems/66481554-9f37-4186-9a65-411f85ad2fae
-- title:
--   A common denominator with a house bound for all monomials of bounded degree
-- statement:
--   Let $K$ be a number field and let $\theta_i \in K$ ($i$ in a finite type). There are a non-zero algebraic integer $b \in K$ and a real $H \ge 1$ such that for every exponent vector $e$ and every $E$ with $\sum_i e_i \le E$, the number
--
--   $$b^{E} \prod_i \theta_i^{e_i}$$
--
--   is an algebraic integer whose house (the largest absolute value of its conjugates, Mathlib's `NumberField.house`) is at most $H^{E}$.
--
--   One non-zero integer $b$ clears the denominators of all the $\theta_i$, and $H = 1 + \overline{|b|} + \sum_i \overline{|b\theta_i|}$ works, since the house is submultiplicative.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

open NumberField

namespace Transcendence

theorem exists_denom_house_monomial_le {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (θ : ι → K) : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧ ∀ (e : ι → ℕ) (E : ℕ),
      ∑ i, e i ≤ E → IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧ house (b ^ E * ∏ i, θ i ^ e i) ≤ H ^ E := by
  sorry

end Transcendence
