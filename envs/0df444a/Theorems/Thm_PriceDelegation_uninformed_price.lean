-- Prove2me | Theorems.Thm_PriceDelegation_uninformed_price
-- name    : PriceDelegation.uninformed_price
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:37.722656+00:00
-- url     : https://prove2.me/theorems/efef8035-e2b8-47a6-bf8a-48485aa37e0d
-- title:
--   §4.3, p. 25 and (EC.4) — the uninformed price $\varphi^*(\lambda)$ exists, is unique, exceeds $\lambda$, and is non-decreasing
-- statement:
--   Assume the valuation has a non-decreasing failure rate (Assumption 2). For every $\lambda\ge0$ the function $\varphi\mapsto(\varphi-\lambda)\bar F(\varphi)$ has exactly one maximizer $\varphi^*(\lambda)$ over $\varphi>0$. It satisfies $\varphi^*(\lambda)>\lambda$, and $\lambda\mapsto\varphi^*(\lambda)$ is non-decreasing on $[0,\infty)$:
--   $$0\le\lambda_1\le\lambda_2\implies\varphi^*(\lambda_1)\le\varphi^*(\lambda_2).$$
--
--   $\varphi^*(\lambda)$ is the best price for a customer whose value is not learned when a sale costs the reservation value $\lambda$; it is the uninformed price of the no-learning and partial-learning policies.
--
--   Differences from the source:
--   - reading: "for all λ", the maximizer over φ > 0 is unique → for all $\lambda\ge0$; reason: the multipliers of §4.3 are $\lambda\ge0$; for $\lambda<0$ no maximizer need exist (Exp(1), $\lambda=-2$: $(\varphi+2)e^{-\varphi}$ is decreasing on $(0,\infty)$)
--   - encoding: (EC.4), the first-order condition $\varphi^*(\lambda)=\lambda+\bar F(\varphi^*(\lambda))/f(\varphi^*(\lambda))$, and "non-decreasing" → the consequences the paper draws from (EC.4): $\varphi^*(\lambda)>\lambda$ and monotonicity; reason: the first-order condition needs a continuous density, which the paper does not assume
--   - generalization: the standing Assumption 1 and $\psi>0$ of the paper → not assumed; reason: the statement holds without them; the paper's case is the special case where they hold
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), p.25 ("φ*(λ) … unique by Assumption 2"); (EC.4) and the sentence after it, p.ec8

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- The uninformed price `φ*(λ)` (Atasu–Ciocan–Désir, Price Delegation with Learning Agents,
SSRN 3931055 (version of Sept. 22, 2021), p.25, and (EC.4), p.ec8). Under Assumption 2, for every
`λ ≥ 0` the maximizer over `φ > 0` of `(φ − λ) · F̄(φ)` exists and is unique; it exceeds `λ`; and
it is a non-decreasing function of `λ`. -/
theorem uninformed_price (V : Valuation) (hA2 : Assumption2 V) :
    (∀ lam : ℝ, 0 ≤ lam → ∃! φ : ℝ, IsUninf V lam φ) ∧
      (∀ lam φ : ℝ, 0 ≤ lam → IsUninf V lam φ → lam < φ) ∧
      (∀ l₁ l₂ φ₁ φ₂ : ℝ, 0 ≤ l₁ → l₁ ≤ l₂ → IsUninf V l₁ φ₁ → IsUninf V l₂ φ₂ → φ₁ ≤ φ₂) := by sorry

end PriceDelegation
