-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_eq_3
-- name    : VerticalOwnership.CheapTalk.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:39.935654+00:00
-- url     : https://prove2.me/theorems/b04174ba-88fd-470a-a515-112ac19f3a3c
-- title:
--   (3), p. 8 — the retailer's expected operational profit is (r − w)(K − ∫_ε̲^{K−μ_i} F) − w∫_ε̲^{q^adv−μ_i} F
-- statement:
--   In the model of the mission, let $i\in\{L,H\}$, and let $q^{adv}$ and $K$ be arbitrary real numbers. The retailer's expected operational profit $\pi_r(q^{adv},K\mid\mu_i)=\mathbb E[(r-w)\min(\mu_i+\varepsilon,K)-w\max(q^{adv}-\mu_i-\varepsilon,0)]$ satisfies
--   $$\pi_r(q^{adv},K\mid\mu_i)=(r-w)\Big(K-\int_{\underline{\varepsilon}}^{K-\mu_i}F(x)\,dx\Big)-w\int_{\underline{\varepsilon}}^{q^{adv}-\mu_i}F(x)\,dx,$$
--   where $F$ is the CDF of $\varepsilon$ and $\underline{\varepsilon}$ the lower end of its support.
--
--   Together with (2), this expresses all four profits entering the cheap-talk threshold through integrals of $F$.
--
--   **Formalization Note** The integrals are oriented: when the upper limit lies below $\underline{\varepsilon}$, the integral is minus the integral over the reversed interval, which vanishes because $F=0$ below $\underline{\varepsilon}$. This is how the printed formula is read for such arguments.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 8, (3); proof p. 42, Appendix E, Proof of equations (2)-(4)

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem eq_3 (M : Model) (hM : M.Standing) (μ q K : ℝ) (hμ : μ = M.μL ∨ μ = M.μH) :
    M.πr μ q K = (M.r - M.w) * (K - ∫ x in M.εlo..K - μ, cdf M.P x) -
      M.w * ∫ x in M.εlo..q - μ, cdf M.P x := by sorry

end VerticalOwnership.CheapTalk
