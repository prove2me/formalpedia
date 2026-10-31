-- Prove2me | Theorems.Thm_RetailTheft_lemma_1
-- name    : RetailTheft.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:15.964997+00:00
-- url     : https://prove2.me/theorems/07fe1645-10f2-4850-8984-667258bc9afd
-- title:
--   Lemma 1 — contracts inducing no ex ante or ex post stealing are without loss: problem (8)
-- statement:
--   Consider the retail-theft model with the standing assumptions, $\theta,\lambda\in[0,1)$. Problem (5)–(7), in which the agent may divert capacity and under-report revenue, can be reformulated as problem (8), in which no stealing occurs and the incentive constraints (LL), (Ex Ante IC), (Ex Post IC) hold:
--
--   1. If $(p,q,R)$ is feasible for (8), then $(p,q,R,q,\mathrm{id})$ is feasible for (5)–(7) — deploying everything and reporting truthfully is a best response of the agent — and its objective in (5) equals its objective in (8).
--   2. For every feasible tuple $(p,q,R,q',\gamma)$ of (5)–(7) there is a contract $(p,q'',\hat R)$ feasible for (8) with
--   $$
--   \mathbb E[\hat R(P_{p,q''})]-cq''\;\ge\;\mathbb E[R(\gamma(P_{p,q'}))]-cq .
--   $$
--
--   This is the paper's "it is without loss of generality to focus on contracts that induce no ex ante or ex post stealing": the two problems have the same value at every price, and the infinite-dimensional agent best-response constraint is replaced by explicit incentive constraints.
--
--   Differences from the source:
--   - reading: p ∈ ℝ₊ (p ≥ 0 in (8)) → p > 0; reason: demand a p^{-b} ε is undefined at p = 0, and Proposition 1 fixes p > 0
--   - reading: ε nonnegative with a known distribution and a well-defined inverse function; a ∈ ℝ₊; c a unit cost → μ a probability measure with μ(−∞,0) = 0 whose cdf is continuous and strictly increasing where 0 < F < 1; a > 0; c > 0; reason: the standard reading of a continuous, invertible demand law; a = 0 or c = 0 is degenerate
--   - reading: θ < 1, λ < 1 → 0 ≤ θ < 1, 0 ≤ λ < 1; reason: stealing efficiencies are nonnegative (the agent earns θc per stolen unit, λ per stolen dollar); Theorems 1–2 fix θ, λ ∈ [0,1)
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
--   - reading: "it is without loss of generality … we can reformulate the principal's problem as (8)" → (i) (8)-feasible contracts are (5)–(7)-feasible with no stealing and the same objective; (ii) every (5)–(7)-feasible tuple is matched or beaten by an (8)-feasible contract; reason: this is the content of "without loss": both problems have the same value
--   - reading: ∀q′ ≤ q in (Ex Ante IC) → ∀q′ ∈ [0, q]; reason: q′ is a deployed capacity
--   - reading: (8) lists (LL), (Ex Ante IC), (Ex Post IC) for R(·) → R is also nondecreasing; reason: R ∈ ℛ by (6), and Lemma 2 takes the contracts of (8) in ℛ; (Ex Post IC) does not imply monotonicity
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, Lemma 1, p. 10 (PDF 10); proof pp. ec1–ec4

import Mathlib
import Definitions.Def_RetailTheft_Model

open MeasureTheory

namespace RetailTheft

/-- **Lemma 1** of Chen, Tian and Zuo, *Optimal Capacity and Price Designs Under Ex Ante and Ex
Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, p. 10 (PDF 10); proof pp. ec1–ec4.
"It is without loss of generality to focus on contracts that induce no ex ante or ex post
stealing, i.e., `q' = q` and `γ(r) = r`. Therefore, we can reformulate the principal's problem as
(8)." Two conclusions, for any `θ, λ ∈ [0, 1)`:
* (i) if `(p, q, R)` is feasible for (8) (with (LL), (Ex Ante IC), (Ex Post IC)), then
  `(p, q, R, q, id)` is feasible for (5)–(7) — no stealing is a best response — and its (5)
  objective equals its (8) objective;
* (ii) for every feasible tuple `(p, q, R, q', γ)` of (5)–(7) there is an (8)-feasible
  `(p, q'', R̂)` whose (8) objective is at least the (5) objective of the tuple.

**Formalization Note** `lam` is `λ`. Prices are positive and reports measurable with values in
`[0, r]` (see `IsFeasible`, `IsReport`); `R` is `Monotone` on `ℝ` (see `IsRepayment`). -/
theorem lemma_1 (M : Params) (hM : M.Standing) (θ lam : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    (∀ (p q : ℝ) (R : ℝ → ℝ), IsFeasible8 M θ lam p q R →
      IsFeasible M θ lam p q R q id ∧ objective M p q R q id = objective8 M p q R) ∧
    (∀ (p q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ), IsFeasible M θ lam p q R q' γ →
      ∃ (q'' : ℝ) (R' : ℝ → ℝ), IsFeasible8 M θ lam p q'' R' ∧
        objective M p q R q' γ ≤ objective8 M p q'' R') := by sorry

end RetailTheft
