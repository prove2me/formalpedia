-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_symmetric_foc
-- name    : RefugeeCash.PDCA.symmetric_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:33.739087+00:00
-- url     : https://prove2.me/theorems/545bd985-4c3a-4963-b0eb-95af63ab099f
-- title:
--   §6.3, eq. (27), p. 22 (PDF 23) — the symmetric PDCA scheme pays k⊙ at p⊙, S = −(∂Π/∂p)/(∂π̃_r/∂k), and the first-order condition holds at p⊙
-- statement:
--   In the symmetric-goods model with $B > 0$, $c > 0$ and Assumption 2, take a target price $p^\odot > c$ and a target cash fraction $k^\odot \in [0,1]$, and let $k(p)$ and $S = S(p^\odot,k^\odot)$ be the PDCA scheme and slope of (27). Then:
--   1. the scheme pays the target fraction at the target price, $k(p^\odot) = k^\odot$;
--   2. the slope is the ratio of the retailer's marginal profits at the target,
--   $$S(p^\odot,k^\odot) = -\,\frac{\partial\Pi(p^\odot,k^\odot)/\partial p}{\partial\Pi(p^\odot,k^\odot)/\partial k},$$
--   which is the paper's $v^{\mathrm{PDCA}}s = -\frac{\partial\Pi}{\partial p}\big/\frac{\partial\tilde\pi_r}{\partial k}$, because with symmetric goods $\tilde\pi_r = \pi_r$ and so $\partial\tilde\pi_r/\partial k = \partial\Pi/\partial k$;
--   3. along the linear part of the scheme the retailer's profit is stationary at the target:
--   $$\frac{d}{dp}\,\Pi\big(p,\ k^\odot + S(p^\odot,k^\odot)(p - p^\odot)\big)\Big|_{p = p^\odot} = 0 .$$
--
--   This is Proposition 4 applied to symmetric goods: the scalar scheme (27) is the policy whose first-order condition is met at $p^\odot$.
--
--   **Formalization Note** The first-order condition is stated for the unclipped linear schedule $k^\odot + S(p - p^\odot)$, which agrees with $k(p)$ near $p^\odot$ whenever $0 < k^\odot < 1$; at $k^\odot \in \{0,1\}$ the clipped schedule need not be differentiable at $p^\odot$. The derivatives are Lean's `deriv`; they are genuine derivatives here because $p^\odot > c$ and Assumption 2 make $\pi_0$ differentiable at $p^\odot$, and $\partial\Pi/\partial k = B(1-c/p^\odot) > 0$.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), p. 22 (PDF 23), §6.3, eq. (27)

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

/-- §6.3, p. 22 (PDF 23), eq. (27): the symmetric PDCA scheme pays `k⊙` at `p⊙`; its slope is
`S(p⊙, k⊙) = −(∂Π/∂p)/(∂π̃r/∂k)` (here `π̃r = πr`, so `∂π̃r/∂k = ∂Π/∂k`); and along the linear part
`k⊙ + S(p⊙, k⊙)(p − p⊙)` of the scheme the retailer's profit has derivative `0` at `p⊙`. -/
theorem symmetric_foc (P : Params) (hP : P.Standing) (pmax p0 : ℝ)
    (hA2 : Assumption2 P pmax p0) (pT kT : ℝ) (hpT : P.c < pT) (hkT : kT ∈ Set.Icc (0 : ℝ) 1) :
    kPDCA P pT kT pT = kT ∧
      slope P pT kT =
        -(deriv (fun p => retailerProfit P p kT) pT /
          deriv (fun k => retailerProfit P pT k) kT) ∧
      HasDerivAt (fun p => retailerProfit P p (kT + slope P pT kT * (p - pT))) 0 pT := by sorry

end RefugeeCash.PDCA
