-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_derivative_low
-- name    : SellingData.AppendsRotation.derivative_low
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:25.597352+00:00
-- url     : https://prove2.me/theorems/d9fb81d3-7a21-4f4f-9db5-d15fceead9e8
-- title:
--   Proof of Proposition 7, p. 33 — ∂Π/∂α_L = θ∫_{c_H}^{c_L} ∂H/∂α_L dv + (1 − θ)[−∫_{c_L}^{v̄} ∂H/∂α_L dv − k′(α_L)]
-- statement:
--   Assume $\partial H(v,\alpha)/\partial\alpha$ is jointly continuous on $[\underline v,\bar v]\times(0,1)$. Let $\alpha\in(\underline\alpha,\bar\alpha)$ be a point at which $k$ has derivative $k'(\alpha)$. Then the low-cost type's benchmark profit $(1-\theta)\big[\int_{c_L}^{\bar v}(v-c_L)\,dH(v,\alpha)-k(\alpha)\big]$ has derivative
--   $$
--   (1-\theta)\Big[-\int_{c_L}^{\bar v}\frac{\partial H(v,\alpha)}{\partial\alpha}\,dv-k'(\alpha)\Big]
--   $$
--   at $\alpha$, and, for every fixed $\alpha_H$, the objective (15) has partial derivative
--   $$
--   \frac{\partial\Pi}{\partial\alpha_L}=\theta\int_{c_H}^{c_L}\frac{\partial H(v,\alpha)}{\partial\alpha}\,dv+(1-\theta)\Big[-\int_{c_L}^{\bar v}\frac{\partial H(v,\alpha)}{\partial\alpha}\,dv-k'(\alpha)\Big]
--   $$
--   at $\alpha_L=\alpha$.
--
--   The two derivatives differ by $\theta\int_{c_H}^{c_L}\partial H/\partial\alpha\,dv$, whose sign the rotation order fixes: negative when $c_L<c_H<v^+$ and positive when $v^+<c_L<c_H$. This comparison is what drives the distortion of $\alpha_L$ in Proposition 7.
--
--   **Formalization Note.** Joint continuity of $\partial H/\partial\alpha$ is a pinned reading of the paper's "continuous and differentiable"; it is what allows differentiating $\int[1-H(v,\alpha)]\,dv$ under the integral sign.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 33, proof of Proposition 7

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- Proof of Proposition 7, p. 33: at an interior `α ∈ (α̲, ᾱ)` where `k` has derivative `k′`,
the benchmark profit of the low-cost type has derivative
`(1 − θ)[−∫_{c_L}^{v̄} ∂H(v, α)/∂α dv − k′(α)]` in `α`, and the objective (15) has derivative
`∂Π/∂α_L = θ ∫_{c_H}^{c_L} ∂H(v, α)/∂α dv + (1 − θ)[−∫_{c_L}^{v̄} ∂H(v, α)/∂α dv − k′(α)]`
in `α_L` (for any `α_H`). -/
theorem derivative_low (M : Model) (hHα : M.HαContinuous) {a k' : ℝ}
    (ha : a ∈ Ioo M.aLo M.aHi) (hk : HasDerivAt M.k k' a) (αH : ℝ) :
    HasDerivAt (fun α => M.benchProfit (1 - M.θ) α M.cL)
        ((1 - M.θ) * (-(∫ v in M.cL..M.vHi, M.Hα v a) - k')) a ∧
      HasDerivAt (fun α => M.reducedProfit αH α)
        (M.θ * (∫ v in M.cH..M.cL, M.Hα v a) +
          (1 - M.θ) * (-(∫ v in M.cL..M.vHi, M.Hα v a) - k')) a := by sorry

end SellingData.AppendsRotation
