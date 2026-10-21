-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_appendix_a_derivatives
-- name    : UtilityTokens.ICOChoice.appendix_a_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:26.055843+00:00
-- url     : https://prove2.me/theorems/3e17cdad-bff2-4c1c-bbb1-9321ec71e1ff
-- title:
--   Appendix A, p. 35 — ∂θ*/∂Θ = (2/3)(1 − (2Θ+1)/(4√(Θ²+Θ+1))) > 0 and θ*/Θ − ∂θ*/∂Θ > 0 for Θ > 0
-- statement:
--   Let $\theta_{\mathrm{int}}(\Theta)=\bigl(2\Theta+1-\sqrt{\Theta^2+\Theta+1}\bigr)/3$ and, for $\Theta>0$,
--   $$d(\Theta)=\frac23\Bigl(1-\frac{2\Theta+1}{4\sqrt{\Theta^2+\Theta+1}}\Bigr).$$
--   Then $\theta_{\mathrm{int}}$ is differentiable at $\Theta$ with derivative $d(\Theta)$, $d(\Theta)>0$, and
--   $$\frac{\theta_{\mathrm{int}}(\Theta)}{\Theta}-d(\Theta)=\frac23+\frac{1-\sqrt{\Theta^2+\Theta+1}}{3\Theta}-d(\Theta)>0 .$$
--
--   These are the first and fourth bullets of Appendix A, used to sign the derivative of $F$.
--
--   **Formalization Note** The appendix writes $\theta^*$, but its bullets hold "$\forall\Theta>0$" and differentiate the closed form $(2\Theta+1-\sqrt{\Theta^2+\Theta+1})/3$; that is the interior root $\theta_{\mathrm{int}}$, which coincides with $\theta^*$ for $\Theta\ge\tilde\Theta$. The statement is made for $\theta_{\mathrm{int}}$.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 35, Appendix A, bullets 1 and 4

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem appendix_a_derivatives (Θ : ℝ) (hΘ : 0 < Θ) :
    let d := 2 / 3 * (1 - (2 * Θ + 1) / (4 * Real.sqrt (Θ ^ 2 + Θ + 1)))
    HasDerivAt thetaInterior d Θ ∧ 0 < d ∧
    thetaInterior Θ / Θ - d =
      2 / 3 + (1 - Real.sqrt (Θ ^ 2 + Θ + 1)) / (3 * Θ) - d ∧
    0 < thetaInterior Θ / Θ - d := by sorry

end UtilityTokens.ICOChoice
