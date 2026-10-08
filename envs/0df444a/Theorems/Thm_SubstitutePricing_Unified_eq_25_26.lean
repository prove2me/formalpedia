-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_eq_25_26
-- name    : SubstitutePricing.Unified.eq_25_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:15.515979+00:00
-- url     : https://prove2.me/theorems/f20b57c9-ace9-46f4-bb43-6db481408b8c
-- title:
--   (25)–(26) — at a stationary point P⁰ = 1/(ξᵘ/(λμ) + 1), ξᵘ > 0 and 0 < P⁰ < 1
-- statement:
--   Assume $\mu>0$ and $0<\lambda\le1$, let $x$ be an inventory level with $S(x)\neq\emptyset$, let $\delta\in\mathbb R^n$, and let $\xi(r)=\sum_{i\in S(x)}\lambda P^i(r)(r-\delta_i)$ be the static objective of the common price. If $r$ is a stationary point of $\xi$, i.e. $\xi'(r)=0$, then, with $P^0=P^0(r,\dots,r)$,
--   $$
--   P^0=\frac{1}{\xi(r)/(\lambda\mu)+1},\qquad \xi(r)=\lambda\mu\Bigl(\frac1{P^0}-1\Bigr),
--   $$
--   and moreover $\xi(r)>0$ and $0<P^0<1$.
--
--   These are the first-order conditions (25)–(26) of the unified pricing problem; the positivity of $\xi^u_t$ at a stationary point is what makes the optimal margin exceed $\mu$.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, App. A, proof of Proposition 1, (25)–(26)

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem eq_25_26 (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ) (hx : (M.S x).Nonempty)
    (δ : Fin M.n → ℝ) (r : ℝ) (hr : HasDerivAt (M.xiS x δ) 0 r) :
    M.P0 x (M.const r) = 1 / (M.xiS x δ r / (M.lam * M.μ) + 1) ∧
    M.xiS x δ r = M.lam * M.μ * (1 / M.P0 x (M.const r) - 1) ∧
    0 < M.xiS x δ r ∧
    0 < M.P0 x (M.const r) ∧ M.P0 x (M.const r) < 1 := by sorry

end SubstitutePricing.Unified
