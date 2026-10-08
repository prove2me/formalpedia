-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_unique_global_maximizer
-- name    : SubstitutePricing.Unified.unique_global_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:45.404987+00:00
-- url     : https://prove2.me/theorems/bf3fff13-1175-4c2a-a70e-e228dbdc84fd
-- title:
--   Second-order condition — ξᵘ has exactly one stationary point, and it is the global maximizer
-- statement:
--   Assume $\mu>0$ and $0<\lambda\le1$, let $x$ be an inventory level with $S(x)\neq\emptyset$, let $\delta\in\mathbb R^n$, and let $\xi(r)=\sum_{i\in S(x)}\lambda P^i(r)(r-\delta_i)$ be the static objective of the common price $r\in\mathbb R$. Then:
--   1. $\xi$ has exactly one stationary point $r$ ($\xi'(r)=0$) on $\mathbb R$;
--   2. at every stationary point $r$ the second derivative is
--   $$
--   \xi''(r)=-\frac\lambda\mu\bigl(1-P^0(r,\dots,r)\bigr)<0,
--   $$
--   and $r$ maximizes $\xi$ over all of $\mathbb R$.
--
--   This is the second-order step of the proof of Proposition 1: $\xi^u_t$ is strictly quasiconcave in the common price, and the solution of the first-order condition (26) is unique and is the global maximizer.
--
--   **Formalization Note.** The existence of a stationary point is part of the claim. The maximization is over all real prices, as in the paper's argument; nonnegativity of the maximizer is a separate matter, needed only in the dynamic program.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, App. A, proof of Proposition 1

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem unique_global_maximizer (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (hx : (M.S x).Nonempty) (δ : Fin M.n → ℝ) :
    (∃! r : ℝ, HasDerivAt (M.xiS x δ) 0 r) ∧
    ∀ r : ℝ, HasDerivAt (M.xiS x δ) 0 r →
      HasDerivAt (deriv (M.xiS x δ)) (-(M.lam / M.μ) * (1 - M.P0 x (M.const r))) r ∧
      IsMaxOn (M.xiS x δ) Set.univ r := by sorry

end SubstitutePricing.Unified
