-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_telescoping_sum
-- name    : PersonalizedAssortment.IB.telescoping_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:21.979656+00:00
-- url     : https://prove2.me/theorems/d0008a81-1616-46e5-a28e-1400bf33351c
-- title:
--   Telescoping: $\sum_{t=1}^T\Psi(I^{t-1}/c)(I^{t-1}-I^t)=\sum_{k=I^T+1}^{c}\Psi(k/c)$
-- statement:
--   Let $\Psi:\mathbb R\to\mathbb R$ be any function and $c$ a natural number. Let $I^0,I^1,\dots,I^T$ be natural numbers with $I^0=c$ that fall by $0$ or $1$ in each step: $I^{t-1}-I^t\in\{0,1\}$ for $1\le t\le T$. Then
--   $$\sum_{t=1}^{T}\Psi\!\left(\frac{I^{t-1}}{c}\right)\left(I^{t-1}-I^{t}\right)\;=\;\sum_{k=I^T+1}^{c}\Psi\!\left(\frac kc\right).$$
--
--   Each unit sold is counted once, at the inventory level just before its sale. This is the pathwise content of the final equality in the paper's computation of the expected dual objective.
--
--   **Formalization Note** The path is indexed from $0$. The left side is written $\sum_{t=0}^{T-1}\Psi(I_t/c)(I_t-I_{t+1})$ with real-valued differences, and the right side sums over the integers $k$ with $I_T<k\le c$.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1549, Section A.3, proof of Theorem 1, first paragraph ('The final equality follows because the kth sold unit ...')

import Mathlib

namespace PersonalizedAssortment.IB

/-- The final equality of the expected-dual display in §A.3 (p. 1549), pathwise: if the inventory
of a product starts at `c` and falls by `0` or `1` in each of `T` periods, then
`∑_{t=1}^T Ψ(I^{t-1}/c)(I^{t-1} - I^t) = ∑_{k=I^T+1}^{c} Ψ(k/c)` (the `k`th sold unit
contributes `Ψ((c - k + 1)/c)`). Periods are indexed from `0` here. -/
theorem telescoping_sum (Ψ : ℝ → ℝ) (c : ℕ) (T : ℕ) (I : ℕ → ℕ) (hI0 : I 0 = c)
    (hstep : ∀ t < T, I (t + 1) ≤ I t ∧ I t ≤ I (t + 1) + 1) :
    ∑ t ∈ Finset.range T, Ψ ((I t : ℝ) / (c : ℝ)) * ((I t : ℝ) - (I (t + 1) : ℝ)) =
      ∑ k ∈ Finset.Ioc (I T) c, Ψ ((k : ℝ) / (c : ℝ)) := by sorry

end PersonalizedAssortment.IB
