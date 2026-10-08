-- Prove2me | Theorems.Thm_RespSourcing_Transparent_rn_dominates_rm
-- name    : RespSourcing.Transparent.rn_dominates_rm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:59.398767+00:00
-- url     : https://prove2.me/theorems/185594f9-20a5-4164-b2c8-6dc0729c13b5
-- title:
--   Appendix, Proposition 1 proof — niche dominates mass market above the threshold
-- statement:
--   Let $\Pi^{RN}$ and $\Pi^{RM}$ be the expected profits of the responsible niche and responsible mass market strategies. Under the standing ranges and $\theta>0$,
--
--   $$r>(v-c_R)\frac{1-\theta}{\theta}\quad\Longrightarrow\quad \Pi^{RN}>\Pi^{RM}.$$
--
--   This is the printed sufficient comparison used when the two strategies sourcing only responsibly remain under consideration.
--
--   **Formalization Note** Positivity of $\theta$ is explicit because the quotient in the paper is undefined at zero.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: RN exceeds RM above the threshold. -/
theorem rn_dominates_rm (p : Params) (hp : p.Standing)
    (hθ : 0 < p.θ)
    (hr : (p.v - p.cR) * ((1 - p.θ) / p.θ) < p.r) :
    profit p .RM < profit p .RN := by sorry

end RespSourcing.Transparent
