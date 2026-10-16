-- Prove2me | Theorems.Thm_RareDisease_ExogOutcome_marginal_rate
-- name    : RareDisease.ExogOutcome.marginal_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:19.267691+00:00
-- url     : https://prove2.me/theorems/12ede1f4-cf37-41cf-9743-67796950802a
-- title:
--   Appendix C, Proof of Proposition 3, p. 37 — (∂W/∂β)/(∂M/∂β) − (∂W/∂α)/(∂M/∂α) = f₁/f₂ with f₂ > 0
-- statement:
--   Let $k>0$, $p\in(0,1)$ and $\alpha,\beta\in[0,1)$. With $W(\alpha,\beta)$ and $M(\alpha,\beta)$ the patient welfare and the government's expenditure of the reduced problem (20),
--   $$W(\alpha,\beta)=\frac{p\,(1-(1-\beta)p)^3}{4(1-\alpha)k},\qquad M(\alpha,\beta)=\frac{\alpha p^2(1-(1-\beta)p)^2}{4(1-\alpha)^2k}+\frac{\beta p^2(1-(1-\beta)p)^2}{2(1-\alpha)k},$$
--   the partial derivatives satisfy
--   $$\frac{\partial W/\partial\beta}{\partial M/\partial\beta}-\frac{\partial W/\partial\alpha}{\partial M/\partial\alpha}=\frac{f_1}{f_2},$$
--   where
--   $$f_1=(1-\alpha)\big((5-\alpha)p-2(1-\alpha)\big)\big(1-(1-\beta)p\big),\qquad f_2=2p(1+2\beta+\alpha-2\alpha\beta)(1+2\alpha p+3\beta p-3\alpha\beta p-\alpha-p),$$
--   and $f_2>0$.
--
--   Along the curve where the budget binds, the left-hand side measures the change in welfare per unit of expenditure when manufacturer subsidy is traded for patient subsidy; its sign is that of $(5-\alpha)p-2(1-\alpha)$, which separates the regimes of Proposition 3.
--
--   **Formalization Note** Partial derivatives are Mathlib's `deriv` of the one-variable sections $\beta'\mapsto W(\alpha,\beta')$ and $\alpha'\mapsto W(\alpha',\beta)$ (and likewise for $M$); both functions are differentiable at every policy, so these are the ordinary partial derivatives. The positivity $f_2>0$ is the paper's step "the sign of $\Delta\pi_g$ is equal to the sign of $[(5-\alpha)p-2(1-\alpha)]$".
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 37, Appendix C, Proof of Proposition 3

import Mathlib

namespace RareDisease.ExogOutcome

/-- Appendix C, Proof of Proposition 3, p. 37: with `W(α, β)` the patient welfare and
`M(α, β)` the government's expenditure of (20), for every policy `α, β ∈ [0,1)`,
`(∂W/∂β)/(∂M/∂β) - (∂W/∂α)/(∂M/∂α) = f₁/f₂` with
`f₁ = (1 - α)((5 - α) p - 2 (1 - α))(1 - (1 - β) p)` and
`f₂ = 2 p (1 + 2β + α - 2αβ)(1 + 2αp + 3βp - 3αβp - α - p)`, and `f₂ > 0`. -/
theorem marginal_rate (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    let W : ℝ → ℝ → ℝ := fun α β => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k)
    let M : ℝ → ℝ → ℝ := fun α β =>
      α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
        + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k)
    let f₁ : ℝ := (1 - α) * ((5 - α) * p - 2 * (1 - α)) * (1 - (1 - β) * p)
    let f₂ : ℝ := 2 * p * (1 + 2 * β + α - 2 * α * β)
      * (1 + 2 * α * p + 3 * β * p - 3 * α * β * p - α - p)
    deriv (fun β' => W α β') β / deriv (fun β' => M α β') β
        - deriv (fun α' => W α' β) α / deriv (fun α' => M α' β) α = f₁ / f₂ ∧
      0 < f₂ := by sorry

end RareDisease.ExogOutcome
