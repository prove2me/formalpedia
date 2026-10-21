-- Prove2me | Theorems.Thm_TokenFinance_Debt_eq_33_strictMono
-- name    : TokenFinance.Debt.eq_33_strictMono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:40.806288+00:00
-- url     : https://prove2.me/theorems/0628b695-6d36-4510-8fce-2662619282e1
-- title:
--   Appendix A, proof of Proposition 2, p. 39 — the left side of (33) runs from −C₀ at δ = 0 to NPV at δ = 1, strictly increasing, with a unique root in (0, 1)
-- statement:
--   Let $0 < c < \theta$ and $C_0 > 0$, and write
--
--   $$
--   F(\delta) = \frac{(\theta-c)^3}{12\theta}\left(-2\delta^3 + 3\delta^2\right) - C_0
--   $$
--
--   for the left-hand side of (33). Then
--
--   1. $F(0) = -C_0$;
--   2. $F(1) = \mathrm{NPV}$, the project's expected net present value (the expected monopoly profit minus $C_0$);
--   3. $F'(\delta) > 0$ for every $\delta \in (0,1)$;
--   4. $F$ is strictly increasing on $[0,1]$;
--   5. if $\mathrm{NPV} > 0$, there is exactly one $\delta \in (0,1)$ with $F(\delta) = 0$.
--
--   This is the step of the proof of Proposition 2 that turns the break-even cubic into a unique repayment; since $\delta < 1$ at the root, the repayment $D = (\theta-c)^2\delta^2/4$ stays below the highest possible monopoly profit $\pi^m(\theta) = (\theta-c)^2/4$.
--
--   **Formalization Note** $F$ is a local `let`; the derivative is Mathlib's `deriv`, which is the true derivative here since $F$ is a polynomial. In item 2, NPV is the integral-defined `npv c C0 θ`, not its closed form.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 39 (PDF p. 40), Appendix A, proof of Proposition 2, paragraph after (33)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem eq_33_strictMono (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0) :
    let F : ℝ → ℝ := fun δ => (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0
    F 0 = -C0 ∧ F 1 = npv c C0 θ ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv F δ) ∧
      StrictMonoOn F (Set.Icc 0 1) ∧
      (0 < npv c C0 θ → ∃! δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 ∧ F δ = 0) := by sorry
end TokenFinance.Debt
