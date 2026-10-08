-- Prove2me | Theorems.Thm_TsayQF_EffQF_cc_optimal
-- name    : TsayQF.EffQF.cc_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:19.748292+00:00
-- url     : https://prove2.me/theorems/ce868a1e-51cf-4ed8-b2ce-ab391cd7a5a9
-- title:
--   §4, p. 1345 (σ_ε = 0) — Q*_CC = F^{-1}((p + s − m)/(p + s − u)) exists and is the unique optimal centralized production
-- statement:
--   Let $p > m > 0$, $u < m$, $s \ge 0$ be the cost data, and let the demand signal $\mu$ have law $\nu$, a probability measure on $\mathbb R$ with finite variance whose distribution function $\Theta$ is differentiable and strictly increasing. With $\sigma_\varepsilon = 0$, market demand equals $\mu$, so $F = \Theta$. A central planner producing $Q$ earns
--   $$\Pi_{CC}(Q) = E_\mu\{p\min[\mu,Q] - s[\mu-Q]^+ + u[Q-\mu]^+\} - mQ .$$
--   Then there is a production $Q$ with $F(Q) = \kappa_S = (p+s-m)/(p+s-u)$, and a production $Q$ maximizes $\Pi_{CC}$ over $\mathbb R$ if and only if
--   $$F(Q) = \frac{p+s-m}{p+s-u}.$$
--   That is, $Q^*_{CC} = F^{-1}((p+s-m)/(p+s-u))$ is the unique optimal production.
--
--   This is the efficiency benchmark of the paper: any decentralized arrangement is system-efficient exactly when it produces $Q^*_{CC}$.
--
--   **Formalization Note.** The page states the result for general $\sigma_\varepsilon$, with $F$ the law of $X=\mu+\varepsilon$; this is the instance $\sigma_\varepsilon = 0$, where $F = \Theta$. "Invertible" is read as strictly increasing on $\mathbb R$; finite variance ($\mu \in L^2(\nu)$) makes every expectation finite.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1345, §4 (instance σ_ε = 0, §7 p. 1350)

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace TsayQF.EffQF

/-- §4, p. 1345, at `σ_ε = 0`: `Q*_CC = F^{-1}((p + s − m)/(p + s − u))` exists and is the unique
optimal centralized production (here `F = Θ`, the cdf of `ν`). -/
theorem cc_optimal (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν) :
    (∃ Q, cdf ν Q = kS D) ∧
      ∀ Q, IsMaxOn (ccProfit D ν) Set.univ Q ↔ cdf ν Q = kS D := by sorry

end TsayQF.EffQF
