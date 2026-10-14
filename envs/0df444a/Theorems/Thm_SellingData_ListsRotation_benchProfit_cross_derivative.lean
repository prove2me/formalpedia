-- Prove2me | Theorems.Thm_SellingData_ListsRotation_benchProfit_cross_derivative
-- name    : SellingData.ListsRotation.benchProfit_cross_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:43.716637+00:00
-- url     : https://prove2.me/theorems/1b5f5e38-25c1-4049-b31e-6b84d19a03e7
-- title:
--   Proof of Proposition 4, p. 32 — $\partial^2\Pi_i/\partial\alpha_i\partial c_i=\theta_i\,\partial H(c_i,\alpha_i)/\partial\alpha_i$, positive below $v^+$, negative above
-- statement:
--   Let $\Pi_i(\alpha,c)=\theta_i\big[\int_c^{\bar v}(v-c)\,dH(v,\alpha)-k(\alpha)\big]$ be the benchmark objective (12) as a function of informativeness $\alpha\in(0,1)$ and cost $c$ in the open support $(\underline v,\bar v)$, for any weight $\theta_i$. Then:
--
--   1. the derivative of $\Pi_i$ in the cost is $\dfrac{\partial\Pi_i}{\partial c}(\alpha,c)=-\theta_i\,[1-H(c,\alpha)]$;
--   2. the derivative of this expression in $\alpha$ is $\theta_i\,\dfrac{\partial H(c,\alpha)}{\partial\alpha}$, so
--   $$\frac{\partial^2\Pi_i}{\partial\alpha_i\,\partial c_i}=\theta_i\,\frac{\partial H(c_i,\alpha_i)}{\partial\alpha_i};$$
--   3. if $\theta_i>0$, this cross derivative is positive for $c<v^+$ and negative for $c>v^+$, by the rotation order (9).
--
--   The sign of the cross derivative is the single-crossing input for the monotone comparative statics of Proposition 4.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 32, proof of Proposition 4

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proof of Proposition 4, p. 32: `∂²Π_i/∂α_i∂c_i = θ_i ∂H(c_i, α_i)/∂α_i`, positive for
`c_i < v⁺` and negative for `c_i > v⁺` by (9). Stated as: the derivative of the benchmark (12)
in the cost is `-θ_i [1 - H(c, α)]`; the derivative of that in `α` is `θ_i ∂H(c, α)/∂α`; and
its sign. -/
theorem benchProfit_cross_derivative (M : Model) (θi : ℝ) :
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ c ∈ Set.Ioo M.vLo M.vHi,
      HasDerivAt (fun x => M.benchProfit θi α x) (-(θi * (1 - M.H c α))) c ∧
      HasDerivAt (fun a => -(θi * (1 - M.H c a))) (θi * M.Hα c α) α ∧
      (0 < θi → (c < M.vPlus → 0 < θi * M.Hα c α) ∧ (M.vPlus < c → θi * M.Hα c α < 0)) := by sorry

end SellingData.ListsRotation
