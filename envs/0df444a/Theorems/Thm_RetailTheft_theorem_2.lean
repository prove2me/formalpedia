-- Prove2me | Theorems.Thm_RetailTheft_theorem_2
-- name    : RetailTheft.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:01.928139+00:00
-- url     : https://prove2.me/theorems/ad21b600-9637-4846-9011-87810bedceab
-- title:
--   Theorem 2 — as ex post stealing becomes more efficient, the optimal price stays flat, falls, then rises, and capacity moves oppositely
-- statement:
--   Let demand be $D_p=a p^{-b}\varepsilon$ with $\varepsilon$ uniform on $[1-\alpha,1+\alpha]$, where $a>0$, $b>1$, $c>0$ and $0<\alpha\le1$. Fix the ex ante stealing efficiency $\theta\in[0,1)$. Then there are two thresholds $\underline\lambda<\bar\lambda\le\theta/(1+\theta)$ in the ex post stealing efficiency $\lambda$, and functions $P,Q$, such that:
--
--   1. for every $\lambda\in[0,1)$, the principal's problem (5)–(7) has a unique optimal price and capacity: $(p,q)$ is an optimal pair if and only if $p=P(\lambda)$ and $q=Q(\lambda)$;
--   2. (a) for $\lambda\le\underline\lambda$ the optimal price and capacity are invariant in $\lambda$;
--   3. (b) for $\lambda\in(\underline\lambda,\bar\lambda]$ the optimal price $P$ strictly decreases and the optimal capacity $Q$ strictly increases in $\lambda$;
--   4. (c) for $\lambda>\bar\lambda$ the optimal price strictly increases and the optimal capacity strictly decreases in $\lambda$.
--
--   Here the optimum is that of the original principal–agent problem: over every nondecreasing revenue-splitting rule with limited liability, every capacity and price, with the agent free to divert capacity and under-report revenue in his best response. The theorem explains why a firm facing more efficient revenue theft may first cut its price and expand capacity, and only later raise its price.
--
--   Differences from the source:
--   - reading: "the optimal price and capacity decisions" → the optimal pair of problem (5)–(7) exists and is unique for every λ ∈ [0,1) (p, q optimal ⇔ p = P λ ∧ q = Q λ); reason: the definite article presupposes a unique optimum; the monotonicity claims are about it
--   - reading: thresholds λ̲ < λ̄ ≤ θ/(1+θ) → arbitrary reals λ̲ < λ̄ ≤ θ/(1+θ), with no 0 ≤ λ̲; reason: at θ = 0, λ̄ ≤ 0 forces λ̲ < 0 and (a) is vacuous; requiring 0 ≤ λ̲ would make the statement false there
--   - encoding: λ < 1 throughout; clauses (a)–(c) for λ in the model's range → (a)–(c) restricted to λ ∈ [0,1); reason: λ is an efficiency in [0,1)
--   - reading: footnote 1: among the agent's best responses, the one that maximizes the principal's utility → optimality is joint maximization over (p, q, R, q′, γ) subject to (q′, γ) being a best response; reason: this is exactly the principal-favourable tie-breaking of footnote 1
--   - reading: ε uniform on [1 − α, 1 + α] for some α ≤ 1 → 0 < α ≤ 1, law (2α)⁻¹·Lebesgue on [1 − α, 1 + α]; reason: at α = 0 the law is a point mass and F̄_p^{-1} is not a root; the paper's displays divide by α
--   - reading: a ∈ ℝ₊, c a unit cost, θ < 1, λ < 1 → a > 0, c > 0, 0 ≤ θ < 1, 0 ≤ λ < 1; reason: degenerate cases excluded; efficiencies are nonnegative and Theorem 2 fixes θ ∈ [0,1)
--   - reading: p ∈ ℝ₊ → p > 0; reason: demand a p^{-b} ε is undefined at p = 0
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, Theorem 2, p. 16 (PDF 16); standing assumptions of §4.2, p. 15; proof pp. ec12–ec13

import Mathlib
import Definitions.Def_RetailTheft_Model
import Definitions.Def_RetailTheft_Uniform

namespace RetailTheft

/-- **Theorem 2** of Chen, Tian and Zuo, *Optimal Capacity and Price Designs Under Ex Ante and Ex
Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, p. 16 (PDF 16); proof pp. ec12–ec13.
Uniform demand `D_p = a p^{-b} ε`, `ε ~ U[1 − α, 1 + α]`, `0 < α ≤ 1` (§4.2, p. 15). Fix
`θ ∈ [0, 1)`. Two thresholds `λ̲ < λ̄ ≤ θ/(1 + θ)` exist in the ex post stealing efficiency such
that, writing `(P λ, Q λ)` for the optimal price and capacity at `λ ∈ [0, 1)`:
* the optimal price and capacity of the principal's problem (5)–(7) exist and are unique:
  `(p, q)` is an optimal pair iff `p = P λ` and `q = Q λ`;
* (a) for `λ ≤ λ̲`, `P` and `Q` are invariant in `λ`;
* (b) on `(λ̲, λ̄]`, `P` strictly decreases and `Q` strictly increases in `λ`;
* (c) for `λ > λ̄`, `P` strictly increases and `Q` strictly decreases in `λ`.

**Formalization Note** `lam` is `λ`, ranging over `[0, 1)`. The optimal pairs are those of the
original problem (5)–(7) (`OptimalPair`: all repayment functions in `ℛ`, all deployed capacities
and measurable reports, agent best response), not of any closed form. The thresholds are
arbitrary reals: at `θ = 0` one has `λ̄ ≤ 0`, so `λ̲ < 0` and (a) is vacuous. -/
theorem theorem_2 (a b c α θ : ℝ) (ha : 0 < a) (hb : 1 < b) (hc : 0 < c) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ (lamLow lamHigh : ℝ) (P Q : ℝ → ℝ),
      lamLow < lamHigh ∧ lamHigh ≤ θ / (1 + θ) ∧
      (∀ lam ∈ Set.Ico (0 : ℝ) 1, ∀ p q : ℝ,
        OptimalPair (uniformModel a b c α) θ lam p q ↔ p = P lam ∧ q = Q lam) ∧
      (∀ lam ∈ Set.Ico (0 : ℝ) 1, ∀ lam' ∈ Set.Ico (0 : ℝ) 1, lam ≤ lamLow → lam' ≤ lamLow →
        P lam = P lam' ∧ Q lam = Q lam') ∧
      StrictAntiOn P (Set.Ioc lamLow lamHigh ∩ Set.Ico 0 1) ∧
      StrictMonoOn Q (Set.Ioc lamLow lamHigh ∩ Set.Ico 0 1) ∧
      StrictMonoOn P (Set.Ioi lamHigh ∩ Set.Ico 0 1) ∧
      StrictAntiOn Q (Set.Ioi lamHigh ∩ Set.Ico 0 1) := by sorry

end RetailTheft
