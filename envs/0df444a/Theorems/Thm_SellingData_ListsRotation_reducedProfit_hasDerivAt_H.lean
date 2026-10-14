-- Prove2me | Theorems.Thm_SellingData_ListsRotation_reducedProfit_hasDerivAt_H
-- name    : SellingData.ListsRotation.reducedProfit_hasDerivAt_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:37.746126+00:00
-- url     : https://prove2.me/theorems/c87fd867-72d9-45bc-a0a8-e4c423ea846e
-- title:
--   Proof of Proposition 5, p. 32 — $\partial\Pi/\partial\alpha_H$ of (14) versus the benchmark derivative
-- statement:
--   Assume $\partial H/\partial\alpha$ is jointly continuous on $[\underline v,\bar v]\times(0,1)$. Let $a\in(\underline\alpha,\bar\alpha)$ be a point where the selling cost $k$ has derivative $k'(a)$, and fix any $\alpha_L$. Then
--
--   1. the benchmark objective $\theta\big[\int_{c_H}^{\bar v}(v-c_H)\,dH(v,\alpha_H)-k(\alpha_H)\big]$ has derivative in $\alpha_H$ at $a$
--   $$\theta\Big[-\int_{c_H}^{\bar v}\frac{\partial H(v,a)}{\partial\alpha_H}\,dv-k'(a)\Big];$$
--   2. the objective of (14) has derivative in $\alpha_H$ at $a$
--   $$\frac{\partial\Pi}{\partial\alpha_H}=\theta\Big[-\int_{c_H}^{\bar v}\frac{\partial H(v,a)}{\partial\alpha_H}\,dv-k'(a)\Big]+(1-\theta)\int_{c_L}^{c_H}\frac{\partial H(v,a)}{\partial\alpha_H}\,dv .$$
--
--   The two derivatives differ by $(1-\theta)\int_{c_L}^{c_H}\partial H/\partial\alpha_H\,dv$, whose sign is fixed by the rotation order when both costs lie on one side of $v^+$; this comparison drives the distortion result of Proposition 5.
--
--   **Formalization Note** Joint continuity of $\partial H/\partial\alpha$ reads the paper's "continuous and differentiable" as continuously differentiable in $\alpha$; it licenses differentiation under the integral sign, which the paper performs without comment.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 32, proof of Proposition 5, second paragraph

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proof of Proposition 5, p. 32: at an interior `α_H` where `k` has derivative `k′(α_H)`, the
benchmark has derivative `θ[-∫_{c_H}^{v̄} ∂H(v, α_H)/∂α_H dv - k′(α_H)]` and (14) has derivative
`∂Π/∂α_H = θ[-∫_{c_H}^{v̄} ∂H(v, α_H)/∂α_H dv - k′(α_H)] + (1 - θ) ∫_{c_L}^{c_H} ∂H(v, α_H)/∂α_H dv`
in `α_H`. Requires `∂H/∂α` to be jointly continuous. -/
theorem reducedProfit_hasDerivAt_H (M : Model) (hHα : M.HαContinuous) (αL a k' : ℝ)
    (ha : a ∈ Set.Ioo M.aLo M.aHi) (hk : HasDerivAt M.k k' a) :
    HasDerivAt (fun α => M.benchProfit M.θ α M.cH)
        (M.θ * (-(∫ v in M.cH..M.vHi, M.Hα v a) - k')) a ∧
      HasDerivAt (fun α => M.reducedProfit α αL)
        (M.θ * (-(∫ v in M.cH..M.vHi, M.Hα v a) - k') +
          (1 - M.θ) * ∫ v in M.cL..M.cH, M.Hα v a) a := by sorry

end SellingData.ListsRotation
