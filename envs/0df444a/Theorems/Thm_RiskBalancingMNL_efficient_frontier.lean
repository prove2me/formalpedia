-- Prove2me | Theorems.Thm_RiskBalancingMNL_efficient_frontier
-- name    : RiskBalancingMNL.efficient_frontier
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:33.790363+00:00
-- url     : https://prove2.me/theorems/4174102b-095c-4f34-b8ca-a26df68b8027
-- title:
--   Theorem 1 and Corollary 1 — efficient frontier: unique equal optimal markup, Lambert W at $\lambda=0$, root of (13) on $(0,\bar\lambda)$, zero on $[\bar\lambda,1)$, decreasing in $\lambda$
-- statement:
--   Fix the MNL model with $n\ge1$ products, qualities $a_i$, costs $c_i$ and price coefficient $b>0$, and consider problem (6): maximize $L_\lambda(m)=\pi(m)^2-\lambda g(m)$ over markup vectors $m\in\mathbb R^n$ with $\pi(m)\ge0$. Let $\bar\lambda=A/(1+A)$ with $A=\sum_ie^{a_i-bc_i}$. Then:
--
--   1. **(Theorem 1(i))** At $\lambda=0$ the equal markup
--   $$
--   m^*(0)=\frac1b\Big(1+W\Big(\sum_ie^{a_i-bc_i-1}\Big)\Big)
--   $$
--   is optimal, and it maximizes the expected profit $\pi$ over all markup vectors.
--   2. **(Theorem 1(ii))** For $\lambda\in(0,\bar\lambda)$ the equation
--   $$
--   \hat m(q_0)-\frac{1}{bq_0}+\frac{\hat m(q_0)}{2[(1-q_0)/\lambda-1]}=0
--   $$
--   has exactly one solution $q_0^*(\lambda)$ in $(0,1-\lambda)$, and the equal markup
--   $$
--   m^*(\lambda)=\frac1b\Big[\log\Big(\sum_ie^{a_i-bc_i}\Big)+\log\frac{q_0^*(\lambda)}{1-q_0^*(\lambda)}\Big]\qquad(15)
--   $$
--   is optimal, with no-purchase probability $q_0^*(\lambda)$.
--   3. **(Theorem 1(iii))** For $\lambda\in[\bar\lambda,1)$ the zero markup $m=0$ (selling at cost) is optimal.
--   4. **(Uniqueness)** For every $\lambda\in[0,1)$ problem (6) has at most one optimal solution.
--   5. **(Equal positive markup)** For $\lambda\in[0,\bar\lambda)$ every optimal solution is an equal markup $(t,\dots,t)$ with $t>0$.
--   6. **(Corollary 1)** For $0\le\lambda<\lambda'<\bar\lambda$, with optimal equal markups $t$ at $\lambda$ and $t'$ at $\lambda'$, $t'<t$ and $q_0(t',\dots,t')<q_0(t,\dots,t)$: the optimal markup and no-purchase probability strictly decrease in $\lambda$.
--
--   Together, the optimal markup runs from the profit-maximizing $m^*(0)$ down to $0$ as risk aversion grows, and is $0$ from $\bar\lambda$ on: this is the efficient frontier of markups.
--
--   **Formalization Note** $W$ is the principal Lambert W function on $[0,\infty)$. Equation (15) is $\hat m(q_0^*(\lambda))$ of (12). Optimality is attainment over all of $\mathbb R^n$ under $\pi\ge0$, so the equal-markup property is part of the conclusion, not an assumption.
--
--   Differences from the source:
--   - generalization: "a unique optimal solution always exists for λ ∈ [0, λ̄]" → uniqueness for every λ ∈ [0, 1); reason: on (λ̄, 1) Theorem 1(iii) only says m = 0 is optimal; uniqueness there is an added conclusion, and the statement specializes to the page's on [0, λ̄]
--   - generalization: m*(0) is "the profit-maximizing markup" → π(m') ≤ π(m*(0)) for every m' ∈ ℝⁿ, not only for π(m') ≥ 0; reason: an infeasible m' has π(m') < 0 ≤ π(m*(0)), so this specializes to the source's claim
--   - generalization: Theorem 1 and Corollary 1 → also: for λ ∈ [0, λ̄) every optimal solution is an equal markup t > 0; reason: an added conclusion (Lemma 1 and the page's "between 0 and m*(0)"); it makes the clauses about constM t in Corollary 1 apply to every optimum
--   - reading: q₀*(λ) "the unique solution" of (13) → the unique solution in (0, 1 − λ); reason: the page restricts to q₀ < 1 − λ by (10); a second root above 1 − λ can exist (A = 1, b = 1, λ = 1/4: near 0.947), and it is not optimal
--   - reading: q₀*(λ) and m*(λ) "decrease in λ" → strictly decrease; reason: the stronger reading; it is true
--   - encoding: problem (6) over shares q ≥ 0 with Σqᵢ ≤ 1 → over markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between m and q (p.9); shares with qᵢ = 0 have no markup mᵢ(q)
--   - encoding: n products → n ≥ 1; reason: with no product λ̄ = 0 and (12) is undefined
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Theorem 1 and Corollary 1 with the sentence "a unique optimal solution always exists for λ ∈ [0, λ̄]", p.12

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Definitions.Def_RiskBalancingMNL_lambertW

namespace RiskBalancingMNL

/-- **Theorem 1 (Profit-maximizing versus Risk-balancing Markups) and Corollary 1 (Efficient
Frontier)**, with the sentence introducing them ("a unique optimal solution always exists"),
Li & Webster, *Optimizing Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of
2021-11-14), p.12. For the MNL model with symmetric price sensitivity and problem (6):
* (a) Theorem 1(i): at `λ = 0` the equal markup `m*(0) = (1/b)(1 + W(Σᵢ e^{aᵢ−bcᵢ−1}))` is
  optimal, and it maximizes the expected profit `π` over all markup vectors;
* (b) Theorem 1(ii): for `λ ∈ (0, λ̄)`, (13) (as printed) has exactly one root `q₀*(λ)` in
  `(0, 1 − λ)`, and the equal markup (15) `m*(λ) = m̂(q₀*(λ))` is optimal with no-purchase
  probability `q₀*(λ)`;
* (c) Theorem 1(iii): for `λ ∈ [λ̄, 1)`, `m = 0` is optimal;
* (d) the optimal solution is unique for every `λ ∈ [0, 1)`;
* (e) for `λ ∈ [0, λ̄)` the optimal solution is an equal markup `t > 0`;
* (f) Corollary 1: for `0 ≤ λ < λ' < λ̄` the optimal markup and no-purchase probability strictly
  decrease.

**Formalization Note** Markups range over all of `ℝⁿ` under `π ≥ 0` (`IsOptimal`); `n ≥ 1`.
`lambertW` is the principal branch on `[0, ∞)`. Eq. (15) is `mHat P x` by definition. -/
theorem efficient_frontier {n : ℕ} [NeZero n] (P : Params n) :
    (IsOptimal P 0
        (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b)) ∧
      ∀ m' : Fin n → ℝ, profit P m' ≤
        profit P (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b))) ∧
    (∀ lam : ℝ, 0 < lam → lam < lamBar P →
      (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0) ∧
      ∀ x ∈ Set.Ioo 0 (1 - lam),
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0 →
        IsOptimal P lam (constM (mHat P x)) ∧ noPurchase P (constM (mHat P x)) = x) ∧
    (∀ lam : ℝ, lamBar P ≤ lam → lam < 1 → IsOptimal P lam (constM 0)) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ m m' : Fin n → ℝ,
      IsOptimal P lam m → IsOptimal P lam m' → m = m') ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < lamBar P → ∀ m : Fin n → ℝ, IsOptimal P lam m →
      ∃ t : ℝ, 0 < t ∧ m = constM t) ∧
    (∀ lam lam' t t' : ℝ, 0 ≤ lam → lam < lam' → lam' < lamBar P →
      IsOptimal P lam (constM t) → IsOptimal P lam' (constM t') →
      t' < t ∧ noPurchase P (constM t') < noPurchase P (constM t)) := by sorry

end RiskBalancingMNL
