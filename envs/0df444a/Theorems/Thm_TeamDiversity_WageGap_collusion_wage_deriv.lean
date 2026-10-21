-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_collusion_wage_deriv
-- name    : TeamDiversity.WageGap.collusion_wage_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:13.133402+00:00
-- url     : https://prove2.me/theorems/9a0a5f81-bee8-4261-bb3d-ca94bd8a37d9
-- title:
--   Proof of Proposition 2, p. 40 — for δ > δ^C, ∂E[w_s**]/∂δ = f_s(2)c/((1 + δ)²(f_s(2) − f_s(1))) > 0
-- statement:
--   Under the standing assumptions, let $w_s^{**}(\delta)$ be, for each $\delta \in [0,1]$, the least feasible wage of the specialized program (with No-cycling). Then for every $\delta \in (\delta^C, 1)$ the expected wage $t \mapsto f_s(2)\,w_s^{**}(t)$ is differentiable at $\delta$, with
--
--   $$\frac{\partial E[w_s^{**}]}{\partial \delta} = \frac{f_s(2)\,c}{(1+\delta)^2\big(f_s(2)-f_s(1)\big)} > 0.$$
--
--   Once collusion binds, the collusion-proof wage rises with patience at this explicit rate.
--
--   **Formalization Note** The open interval $(\delta^C,1)$ is used so that the derivative is two-sided; $w_s^{**}$ is only pinned down on $[0,1]$.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), proof of Proposition 2, p. 40 (PDF 41)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Proof of Proposition 2, p. 40: for `δ > δ^C`,
`∂E[w_s**]/∂δ = f_s(2)c / ((1 + δ)²(f_s(2) − f_s(1))) > 0`. -/
theorem collusion_wage_deriv (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) (ws : ℝ → ℝ)
    (hws : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasS c fs δ) (ws δ)) :
    ∀ δ ∈ Set.Ioo (deltaC fs) 1,
      HasDerivAt (fun t => expWage fs (ws t))
          (fs.f2 * c / ((1 + δ) ^ 2 * (fs.f2 - fs.f1))) δ ∧
        0 < fs.f2 * c / ((1 + δ) ^ 2 * (fs.f2 - fs.f1)) := by sorry

end TeamDiversity.WageGap
