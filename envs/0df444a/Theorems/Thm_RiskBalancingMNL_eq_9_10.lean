-- Prove2me | Theorems.Thm_RiskBalancingMNL_eq_9_10
-- name    : RiskBalancingMNL.eq_9_10
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:44:17.818133+00:00
-- url     : https://prove2.me/theorems/70b2ae3e-d9d2-4a79-93bc-4fd75d29ce6e
-- title:
--   Eqs (9)–(10) — the equal-markup objective, and $q_0<1-\lambda$ at the optimum (corrected: $\lambda<\bar\lambda$)
-- statement:
--   Fix the MNL model with $n\ge1$ products.
--
--   1. (9) For every $\lambda$ and every equal markup $t$,
--   $$
--   L_\lambda(t,\dots,t)=\Big(t\sum_iq_i\Big)^2-\lambda t^2\sum_iq_i=t^2\Big(\sum_iq_i\Big)\Big(\sum_iq_i-\lambda\Big)=t^2(1-q_0)(1-q_0-\lambda).
--   $$
--   2. The equal markup $t$ is feasible ($\pi\ge0$) exactly when $t\ge0$, so problem (6) becomes $\max\,t^2(1-q_0)(1-q_0-\lambda)$ subject to $t\ge0$.
--   3. (10) For $\lambda\in[0,\bar\lambda)$, every optimal solution $m$ of (6) satisfies
--   $$
--   q_0(m)<1-\lambda .
--   $$
--
--   Part 3 says that a profitable risk-averse firm must capture a total market share above $\lambda$.
--
--   Differences from the source:
--   - correction: (10) holds "under the optimal pricing solution", with no range of λ → (10) for λ ∈ [0, λ̄); reason: for λ ≥ λ̄ the optimum is m = 0 (Theorem 1(iii)), where q₀ = 1 − λ̄ ≥ 1 − λ; instance n = 1, a₁ = c₁ = 0, b = 1, λ = 3/4: the optimum m = 0 has q₀ = 1/2 > 1/4 = 1 − λ
--   - reading: max_q m²(1 − q₀)(1 − q₀ − λ) s.t. m ≥ 0 → an equal markup t is feasible (π ≥ 0) iff t ≥ 0; reason: at equal markup π = t(1 − q₀) with 1 − q₀ > 0, so the constraint π ≥ 0 of (6) is m ≥ 0
--   - encoding: n products → n ≥ 1; reason: with no product π = 0 and every t would be feasible
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), eqs (9) and (10) with the sentence following (9), p.11

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat

namespace RiskBalancingMNL

/-- **Eqs (9) and (10)**, Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice
Models*, SSRN 3959428 (PDF of 2021-11-14), p.11.
1. (9): at an equal markup `t`,
   `L = (t Σᵢ qᵢ)² − λ t² Σᵢ qᵢ = t²(Σᵢ qᵢ)(Σᵢ qᵢ − λ) = t²(1 − q₀)(1 − q₀ − λ)`.
2. The rewritten problem: an equal markup `t` is feasible (`π ≥ 0`) iff `t ≥ 0`.
3. (10), corrected to `λ ∈ [0, λ̄)`: at an optimal solution, `q₀ < 1 − λ`.

**Formalization Note** The page states (10) with no range of `λ`. For `λ ∈ [λ̄, 1)` the optimum is
`m = 0` (Theorem 1(iii)) with `q₀ = 1 − λ̄ ≥ 1 − λ`, so (10) is stated for `λ ∈ [0, λ̄)`. -/
theorem eq_9_10 {n : ℕ} [NeZero n] (P : Params n) :
    (∀ lam t : ℝ,
      objective P lam (constM t) =
        (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i ∧
      (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i =
        t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) ∧
      t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) =
        t ^ 2 * (1 - noPurchase P (constM t)) * (1 - noPurchase P (constM t) - lam)) ∧
    (∀ t : ℝ, Feasible P (constM t) ↔ 0 ≤ t) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < lamBar P → ∀ m : Fin n → ℝ, IsOptimal P lam m →
      noPurchase P m < 1 - lam) := by sorry

end RiskBalancingMNL
