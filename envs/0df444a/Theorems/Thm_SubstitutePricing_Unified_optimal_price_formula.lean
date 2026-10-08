-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_optimal_price_formula
-- name    : SubstitutePricing.Unified.optimal_price_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:04.612375+00:00
-- url     : https://prove2.me/theorems/3d3f0b47-f840-497d-91d3-17583381faf5
-- title:
--   r* = Δʷπ + m with m = μ/P⁰*, and m solves (m/μ − 1)exp((m+u₀)/μ) = exp((a_w − Δʷπ)/μ)
-- statement:
--   Assume $\mu>0$ and $0<\lambda\le1$, let $x$ be an inventory level with $S(x)\neq\emptyset$, let $\delta\in\mathbb R^n$, and let $r$ be a stationary point of the static objective $\xi(r)=\sum_{i\in S(x)}\lambda P^i(r)(r-\delta_i)$ of the common price. Put $m=\mu/P^0(r,\dots,r)$ and
--   $$
--   \delta_w=\frac{\sum_{i\in S(x)}e^{a_i/\mu}\delta_i}{\sum_{i\in S(x)}e^{a_i/\mu}},\qquad a_w=\mu\ln\sum_{i\in S(x)}e^{a_i/\mu}.
--   $$
--   Then
--   $$
--   r=\delta_w+m\qquad\text{and}\qquad \Bigl(\frac m\mu-1\Bigr)\exp\Bigl(\frac{m+u_0}\mu\Bigr)=\exp\Bigl(\frac{a_w-\delta_w}{\mu}\Bigr).
--   $$
--
--   With $\delta_i=\Delta^i\pi_{t-1}(x)$, $\delta_w$ is $\Delta^w\pi_{t-1}(x)$ and this is the formula $r^*_t=\Delta^w\pi_{t-1}(x_t)+m_t$ of the proof of Proposition 1, together with the equation that determines $m_t$.
--
--   **Formalization Note.** The paper's intermediate display (27) is misprinted (it has $(m_t/\mu-1)\sum_i\exp(-a_i/\mu)$ where $(m_t/\mu-1)/\sum_i\exp(a_i/\mu)$ is meant); only the conclusions, which are stated correctly on the page, are formalized.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, App. A, proof of Proposition 1, (27)–(28) and the following displays

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem optimal_price_formula (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (hx : (M.S x).Nonempty) (δ : Fin M.n → ℝ) (r : ℝ) (hr : HasDerivAt (M.xiS x δ) 0 r) :
    r = M.wavg x δ + M.μ / M.P0 x (M.const r) ∧
    M.marginLHS (M.μ / M.P0 x (M.const r)) =
      Real.exp ((M.aW x - M.wavg x δ) / M.μ) := by sorry

end SubstitutePricing.Unified
