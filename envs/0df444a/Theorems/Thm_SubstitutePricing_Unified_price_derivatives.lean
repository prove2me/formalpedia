-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_price_derivatives
-- name    : SubstitutePricing.Unified.price_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:59.327474+00:00
-- url     : https://prove2.me/theorems/bd7629d4-b602-4718-8ad2-690c764e78dc
-- title:
--   Derivatives of Pⁱ, P⁰ and ξᵘ in the common price
-- statement:
--   Assume $\mu>0$ and $0<\lambda\le1$. Fix an inventory level $x$, numbers $\delta_i$ ($i\in S(x)$) and a common price $r\in\mathbb R$, and write $P^i(r),P^0(r)$ for the MNL probabilities at the price vector $(r,\dots,r)$ and
--   $$
--   \xi(r)=\sum_{i\in S(x)}\lambda P^i(r)\,(r-\delta_i).
--   $$
--   Then
--   1. $\dfrac{dP^i}{dr}=-\dfrac1\mu P^iP^0$ for every $i\in S(x)$;
--   2. $\dfrac{dP^0}{dr}=\dfrac1\mu P^0(1-P^0)$;
--   3. $\dfrac{d\xi}{dr}=\lambda\sum_{i\in S(x)}\Bigl(P^i-\dfrac1\mu P^iP^0(r-\delta_i)\Bigr)$;
--   4. and this derivative equals
--   $$
--   \lambda(1-P^0)-\frac1\mu P^0\,\xi(r).
--   $$
--
--   With $\delta_i=\Delta^i\pi_{t-1}(x)$, $\xi$ is the paper's $\xi^u_t(x,\cdot)$ of (24); these derivatives give its first-order condition.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, App. A, proof of Proposition 1

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem price_derivatives (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (δ : Fin M.n → ℝ) (r : ℝ) :
    (∀ i ∈ M.S x, HasDerivAt (fun s : ℝ => M.P x (M.const s) i)
        (-(1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r)) r) ∧
    HasDerivAt (fun s : ℝ => M.P0 x (M.const s))
        ((1 / M.μ) * M.P0 x (M.const r) * (1 - M.P0 x (M.const r))) r ∧
    HasDerivAt (M.xiS x δ)
        (M.lam * ∑ i ∈ M.S x, (M.P x (M.const r) i -
          (1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r) * (r - δ i))) r ∧
    M.lam * ∑ i ∈ M.S x, (M.P x (M.const r) i -
          (1 / M.μ) * M.P x (M.const r) i * M.P0 x (M.const r) * (r - δ i)) =
      M.lam * (1 - M.P0 x (M.const r)) - (1 / M.μ) * M.P0 x (M.const r) * M.xiS x δ r := by sorry

end SubstitutePricing.Unified
