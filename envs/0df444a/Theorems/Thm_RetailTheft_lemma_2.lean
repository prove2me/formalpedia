-- Prove2me | Theorems.Thm_RetailTheft_lemma_2
-- name    : RetailTheft.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:31.336985+00:00
-- url     : https://prove2.me/theorems/8c158952-f36e-4d7a-8beb-2f42fcef37c4
-- title:
--   Lemma 2 (corrected: replicated or improved) — threshold commissions $R_{\bar r}$ suffice
-- statement:
--   Consider the retail-theft model with the standing assumptions and $\theta,\lambda\in[0,1)$. Let the contract $(p,q,R)$ satisfy (LL), (Ex Ante IC) and (Ex Post IC) of problem (8). Then there is a threshold $\bar r\in[0,pq]$ such that
--
--   1. $(p,q,R_{\bar r})$, with $R_{\bar r}(r)=(1-\lambda)(r\wedge\bar r)$, again satisfies (LL), (Ex Ante IC) and (Ex Post IC);
--   2. $\mathbb E[R(P_{p,q})]\le\mathbb E[R_{\bar r}(P_{p,q})]$;
--   3. if $\mathbb E[R(P_{p,q})]\ge0$, then $\mathbb E[R_{\bar r}(P_{p,q})]=\mathbb E[R(P_{p,q})]$.
--
--   So the principal's objective in (8) attained by any incentive-compatible contract is replicated, or improved, by a threshold commission at the same price and capacity, and the search over commission schemes reduces to one dimension.
--
--   Differences from the source:
--   - correction: the objective of (p,q,R) can be replicated with (p,q,R_r̄) for some r̄ ∈ [0,pq] → replicated when E[R(P_{p,q})] ≥ 0, and replicated or improved in general; reason: every R_r̄ has E[R_r̄(P_{p,q})] ≥ 0, while R ≡ −1 is feasible: uniform ε with α = 1/2, a = 1, b = 2, c = 1, θ = 1/2, λ = 1/5, p = 4, q = 1/100 satisfies (LL), (Ex Ante IC), (Ex Post IC) with E[R(P)] = −1 (proved in the verification file)
--   - reading: p ∈ ℝ₊ (p ≥ 0 in (8)) → p > 0; reason: demand a p^{-b} ε is undefined at p = 0, and Proposition 1 fixes p > 0
--   - reading: ε nonnegative with a known distribution and a well-defined inverse function; a ∈ ℝ₊; c a unit cost → μ a probability measure with μ(−∞,0) = 0 whose cdf is continuous and strictly increasing where 0 < F < 1; a > 0; c > 0; reason: the standard reading of a continuous, invertible demand law; a = 0 or c = 0 is degenerate
--   - reading: θ < 1, λ < 1 → 0 ≤ θ < 1, 0 ≤ λ < 1; reason: stealing efficiencies are nonnegative (the agent earns θc per stolen unit, λ per stolen dollar); Theorems 1–2 fix θ, λ ∈ [0,1)
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, Lemma 2, p. 11 (PDF 11); proof pp. ec5–ec6

import Mathlib
import Definitions.Def_RetailTheft_Model

open MeasureTheory

namespace RetailTheft

/-- **Lemma 2** (corrected: replicated or improved) of Chen, Tian and Zuo, *Optimal Capacity and
Price Designs Under Ex Ante and Ex Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, p. 11
(PDF 11); proof pp. ec5–ec6. For every contract `(p, q, R)` satisfying (LL), (Ex Ante IC) and
(Ex Post IC) there is `r̄ ∈ [0, pq]` such that the threshold commission `R_r̄` of (9) gives a
contract `(p, q, R_r̄)` that is again feasible for (8), with
`E[R(P_{p,q})] ≤ E[R_r̄(P_{p,q})]`, and with equality whenever `E[R(P_{p,q})] ≥ 0`.

**Formalization Note** The printed lemma claims exact replication. That fails when
`E[R(P_{p,q})] < 0`: every `R_r̄` has `E[R_r̄(P_{p,q})] ≥ 0`, while `R ≡ −1` is feasible (e.g.
uniform `ε` with `α = 1/2`, `a = 1`, `b = 2`, `c = 1`, `θ = 1/2`, `λ = 1/5`, `p = 4`,
`q = 1/100`). The statement is corrected to "replicated or improved". -/
theorem lemma_2 (M : Params) (hM : M.Standing) (θ lam : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (p q : ℝ) (R : ℝ → ℝ)
    (hR : IsFeasible8 M θ lam p q R) :
    ∃ rbar ∈ Set.Icc 0 (p * q),
      IsFeasible8 M θ lam p q (thresholdR lam rbar) ∧
      (∫ ε, R (revenue M p q ε) ∂M.μ) ≤ ∫ ε, thresholdR lam rbar (revenue M p q ε) ∂M.μ ∧
      (0 ≤ ∫ ε, R (revenue M p q ε) ∂M.μ →
        ∫ ε, thresholdR lam rbar (revenue M p q ε) ∂M.μ =
          ∫ ε, R (revenue M p q ε) ∂M.μ) := by sorry

end RetailTheft
