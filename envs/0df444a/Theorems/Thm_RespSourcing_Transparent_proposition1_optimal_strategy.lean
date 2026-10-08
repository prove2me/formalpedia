-- Prove2me | Theorems.Thm_RespSourcing_Transparent_proposition1_optimal_strategy
-- name    : RespSourcing.Transparent.proposition1_optimal_strategy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:24.844229+00:00
-- url     : https://prove2.me/theorems/be1c69bc-043b-4b41-9161-0524a2241aad
-- title:
--   Proposition 1 — sufficient conditions for the four optimal sourcing strategies
-- statement:
--   Let $v$ be baseline valuation, $r$ the responsible-sourcing premium, $\theta$ the socially conscious fraction, $\alpha$ its fraction that exits following a violation, $\phi$ the violation probability, $c_R$ and $c_{NR}$ the responsible and risky marginal costs, and $c_{VP}$ the fixed violation penalty. Assume $0\le\theta,\alpha,\phi\le1$ and $c_{NR}<c_R$. Set $\Delta=c_R-c_{NR}$ and $[x]^+=\max(x,0)$. A strategy is optimal when its Table 2 profit is at least every one of the four profits.
--
--   Proposition 1 gives four sufficient conditions:
--
--   1. **Low-cost sourcing** is optimal when
--
--      $$r<\Delta,\qquad \phi[\alpha\theta(v-c_{NR})+c_{VP}]<\Delta-[\theta r-(1-\theta)(v-c_R)]^+.$$
--
--   2. **Dual sourcing** is optimal when
--
--      $$r>\Delta,\qquad \phi[\alpha\theta(v+r-c_{NR})+c_{VP}]<\Delta(1-\theta)+\theta r-[\theta r-(1-\theta)(v-c_R)]^+.$$
--
--   3. **Responsible niche sourcing** is optimal when $\theta>0$, neither low-cost nor dual sourcing is optimal, and
--
--      $$r>(v-c_R)\frac{1-\theta}{\theta}.$$
--
--   4. **Responsible mass market sourcing** is optimal when $\theta>0$, neither low-cost nor dual sourcing is optimal, and
--
--      $$r<(v-c_R)\frac{1-\theta}{\theta}.$$
--
--   This proposition identifies when each supplier configuration maximizes expected profit among the four strategies.
--
--   **Formalization Note** Part (ii) preserves the printed $c_{NR}$; the appendix's pairwise dual-sourcing comparisons contain $c_R$ in that position. The printed hypothesis is stronger under the standing ranges. Parts (iii) and (iv) explicitly require $\theta>0$ so their quotient is defined.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2729, Proposition 1; proof p. 2742; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Proposition 1, p. 2729, all four sufficient conditions, with part (ii) as printed. -/
theorem proposition1_optimal_strategy (p : Params) (hp : p.Standing) :
    (p.r < p.Δ →
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) <
        p.Δ - max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 →
      IsOptimal p .LC) ∧
    (p.Δ < p.r →
      p.φ * (p.α * p.θ * (p.v + p.r - p.cNR) + p.cVP) <
        p.Δ * (1 - p.θ) + p.θ * p.r -
          max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 →
      IsOptimal p .DS) ∧
    (0 < p.θ →
      (p.v - p.cR) * (1 - p.θ) / p.θ < p.r →
      ¬ IsOptimal p .LC → ¬ IsOptimal p .DS → IsOptimal p .RN) ∧
    (0 < p.θ →
      p.r < (p.v - p.cR) * (1 - p.θ) / p.θ →
      ¬ IsOptimal p .LC → ¬ IsOptimal p .DS → IsOptimal p .RM) := by sorry

end RespSourcing.Transparent
