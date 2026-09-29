-- Prove2me | Theorems.Thm_SeasonalPricing_Contingent_waitingSurplus_slope_lt_one
-- name    : SeasonalPricing.Contingent.waitingSurplus_slope_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:09:58.111798+00:00
-- url     : https://prove2.me/theorems/eaccb225-eee6-409f-9fbd-b9eca8ed4ac7
-- title:
--   Proof of Theorem 1 — the right-hand side of (2) is nonnegative, nondecreasing, with slope below one
-- statement:
--   Let $(\pi, a)$ be a belief about the remaining inventory $Q_T \in \{0,\dots,Q\}$ and the allocation event $\mathcal A$, let $p_2(\cdot)$ be any discount menu, $\alpha \ge 0$, $0 \le t < T$, and write $\delta = e^{-\alpha(T-t)} \in (0, 1]$ and
--
--   $$
--   W(\psi) = \sum_{q=0}^{Q} \pi(q)\,a(q)\,\max\{\psi\delta - p_2(q), 0\}, \qquad S(\psi) = \sum_{q \le Q,\ p_2(q) \le \psi\delta} \pi(q)\,a(q) = \Pr\{\psi\delta \ge p_2(Q_T), \mathcal A\}.
--   $$
--
--   Assume that $\alpha > 0$ or that allocation is not sure, $\sum_{q=0}^{Q}\pi(q)a(q) < 1$. Then for all $\psi \le \psi'$:
--
--   $$
--   0 \le W(\psi) \le W(\psi'), \qquad \delta\,(\psi' - \psi)\,S(\psi) \;\le\; W(\psi') - W(\psi) \;\le\; \delta\,(\psi' - \psi)\,S(\psi'),
--   $$
--
--   and for every $\psi$, $\delta\, S(\psi) < 1$.
--
--   This is the displayed step of the paper's proof of Theorem 1: the right-hand side of (2) is nonnegative and increasing, with derivative $e^{-\alpha(T-t)}\Pr\{\psi e^{-\alpha(T-t)} \ge p_2(Q_T), \mathcal A\} < 1$. Together with the unit slope of the left-hand side $\psi - p_1$, it yields the uniqueness of the solution of (2).
--
--   **Formalization Note** $W$ is piecewise linear with kinks where $\psi\delta = p_2(q)$, so the paper's derivative is read as the two-sided bracket on increments above: the right derivative at $\psi$ is $\delta S(\psi)$ and the left derivative at $\psi'$ is at most $\delta S(\psi')$. The hypothesis "$\alpha > 0$ or $\sum \pi a < 1$" is not in the paper: the paper's "$< 1$" fails when $\alpha = 0$ and allocation is sure, because then $\delta = 1$ and $\Pr\{\psi \ge p_2(Q_T), \mathcal A\} = 1$ for large $\psi$. The paper's pricing scheme has $p_2(q) \le p_1$; this step does not use it and holds for any menu.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 358, Proof of Theorem 1 (the derivative display)

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

namespace SeasonalPricing.Contingent

/-- Proof of Theorem 1 (Aviv–Pazgal 2008, p. 358), the slope display: the right-hand side
`W(ψ)` of (2) is nonnegative and nondecreasing in `ψ`, its increments are bracketed by
`e^{-α(T-t)} · Pr{ψ e^{-α(T-t)} ≥ p₂(Q_T), 𝒜}` evaluated at the two endpoints (the one-sided
derivatives), and that slope is strictly below one. -/
theorem waitingSurplus_slope_lt_one (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    (∀ ψ ψ' : ℝ, ψ ≤ ψ' →
      0 ≤ waitingSurplus Q pmf alloc p2 α T t ψ ∧
      waitingSurplus Q pmf alloc p2 α T t ψ ≤ waitingSurplus Q pmf alloc p2 α T t ψ' ∧
      Real.exp (-(α * (T - t))) * (ψ' - ψ) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ * Real.exp (-(α * (T - t)))), pmf q * alloc q)
        ≤ waitingSurplus Q pmf alloc p2 α T t ψ' - waitingSurplus Q pmf alloc p2 α T t ψ ∧
      waitingSurplus Q pmf alloc p2 α T t ψ' - waitingSurplus Q pmf alloc p2 α T t ψ
        ≤ Real.exp (-(α * (T - t))) * (ψ' - ψ) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ' * Real.exp (-(α * (T - t)))), pmf q * alloc q)) ∧
    (∀ ψ : ℝ,
      Real.exp (-(α * (T - t))) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ * Real.exp (-(α * (T - t)))), pmf q * alloc q) < 1) := by sorry

end SeasonalPricing.Contingent
