-- Prove2me | Theorems.Thm_TsayQF_EffQF_proposition_6a
-- name    : TsayQF.EffQF.proposition_6a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:21.523597+00:00
-- url     : https://prove2.me/theorems/4f7407a2-92b9-4117-9557-23b0456b7077
-- title:
--   Proposition 6(a), p. 1350 — with σ_ε = 0, the QF contract with flexibility ψ and transfer price c̄(ψ) of (4) is system-efficient
-- statement:
--   Let $p > m > 0$, $u < m$, $s \ge 0$ be the cost data, and let the demand signal $\mu$ have law $\nu$, a probability measure on $\mathbb R$ with finite variance whose distribution function $F = \Theta$ is differentiable and strictly increasing; with $\sigma_\varepsilon = 0$ market demand equals $\mu$. Let $Q^*_{CC} > 0$ satisfy $F(Q^*_{CC}) = (p+s-m)/(p+s-u)$, i.e. $Q^*_{CC} = F^{-1}((p+s-m)/(p+s-u))$. Take QF parameters $0\le\omega<1$, $\alpha\ge-\omega$, total flexibility $\psi = (1+\alpha)/(1-\omega)$, and the transfer price
--   $$\bar c(\psi) = u + \frac{m-u}{\dfrac1\psi F\!\left(\dfrac1\psi F^{-1}\!\left(\dfrac{p+s-m}{p+s-u}\right)\right) + \dfrac{m-u}{p+s-u}} . \tag{4}$$
--   Let $\hat q = Q^*_{CC}/(1+\alpha)$. Under the QF contract $\{\bar c(\psi),(\alpha,\omega)\}$:
--   1. a forecast $q \ge 0$ maximizes the retailer's expected profit $q\mapsto\pi_{R,QF}(q,q(1+\alpha))$ over $[0,\infty)$ if and only if $q = \hat q$;
--   2. given the forecast $\hat q$, a production $Q \ge \hat q(1+\alpha)$ maximizes the EM's expected profit (2) over $[\hat q(1+\alpha),\infty)$ if and only if $Q = \hat q(1+\alpha) = Q^*_{CC}$;
--   3. the resulting expected system profit is at least the central planner's expected profit at every production level:
--   $$\Pi_{CC}(Q) \le \pi_{R,QF}(\hat q,\hat q(1+\alpha)) + \pi_{EM,QF}(\hat q(1+\alpha);\hat q) \quad\text{for all } Q.$$
--
--   Together, the equilibrium of the QF contract puts the efficient quantity $Q^*_{CC}$ into the system and makes all of it available to the market, which is what the paper calls system efficiency. A menu of efficient contracts is obtained by varying $\psi$ and charging $\bar c(\psi)$.
--
--   **Formalization Note.** $F^{-1}$ is not used as a function: $Q^*_{CC}$ is a real number with the hypothesis $F(Q^*_{CC}) = \kappa_S$, which determines it uniquely since $F$ is strictly increasing, and (4) is kept in its printed form. The retailer's forecast objective fixes the EM's production at $q(1+\alpha)$, as §6.1 does after Proposition 2; clause 2 checks that the EM indeed wants to build exactly that amount at this contract. The full game in which the retailer could anticipate other EM responses is not modelled. The hypothesis $Q^*_{CC} > 0$ makes explicit the paper's presumption that demand is almost certainly nonnegative (§3.3); without it no forecast $q \ge 0$ could produce $Q^*_{CC}$. The bound $\omega<1$ is Proposition 3's standing case, where $\psi$ is finite. $\bar c(\psi)$ can exceed $p$ when $s>0$; no restriction $\bar c(\psi) < p$ is imposed.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1350, Proposition 6(a), display (4); with p. 1348, Proposition 2 and §7, pp. 1349–1350

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace TsayQF.EffQF

/-- Proposition 6(a), p. 1350: when `σ_ε = 0`, the QF contract `{c̄(ψ), (α, ω)}` with
`ψ = (1 + α)/(1 − ω)` and `c̄` given by (4) is system-efficient: the retailer's unique optimal
forecast is `q̂ = Q*_CC/(1 + α)`, the EM's unique optimal production is then `q̂(1 + α) = Q*_CC`,
and the resulting expected system profit equals the centralized optimum. -/
theorem proposition_6a (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hα : -ω ≤ α)
    (Qcc : ℝ) (hQcc : cdf ν Qcc = kS D) (hpos : 0 < Qcc) :
    let c := cbar D ν (psi α ω) Qcc
    let qhat := Qcc / (1 + α)
    (∀ q, 0 ≤ q → (IsMaxOn (forecastProfit D ν c α ω) (Set.Ici 0) q ↔ q = qhat)) ∧
    (∀ Q, qhat * (1 + α) ≤ Q →
      (IsMaxOn (emProfit D ν c ω qhat) (Set.Ici (qhat * (1 + α))) Q ↔ Q = qhat * (1 + α))) ∧
    (∀ Q, ccProfit D ν Q ≤
      forecastProfit D ν c α ω qhat + emProfit D ν c ω qhat (qhat * (1 + α))) := by sorry

end TsayQF.EffQF
