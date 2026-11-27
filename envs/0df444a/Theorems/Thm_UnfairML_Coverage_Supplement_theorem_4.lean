-- Prove2me | Theorems.Thm_UnfairML_Coverage_Supplement_theorem_4
-- name    : UnfairML.Coverage.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:37:23.298689+00:00
-- url     : https://prove2.me/theorems/6eb0e56a-94f6-4163-ab50-43d89a35119e
-- title:
--   Theorem 4 (corrected: positive utilities) — optimal learning is nonincreasing in the fairness parameter
-- statement:
--   Let the two-group parameters satisfy $\alpha,\beta>0$, $0<d_r<d_p<1$, $\alpha_r\le\beta_r$ and $0<\gamma_p<\gamma_r$. Keep any convex nondecreasing learning cost $\tau$ fixed. For $1\le\theta_1<\theta_2$, let $s_i$ be any attained global maximum of (13) at $\theta_i$, over the active branch $c_r=1-\gamma_r s$, $c_p=1-\theta_i\gamma_r s$ with $0\le s\le1/(2\gamma_r)$ and $\gamma_p s\le c_p\le1-\gamma_p s$. Then
--   $$s_2\le s_1.$$
--   The ordering includes zero effort and boundary plateaus. At an identical parameter the same chosen optimizer is used on both sides, giving equality; the theorem compares arbitrary optima at strictly ordered parameters. No differentiable optimizer selection or first-order optimality hypothesis is assumed.
--
--   Differences from the source:
--   - correction: Table 1 calls α and β utility and dis-utility without explicitly imposing positivity → α>0 and β>0 through the published Standing predicate; reason: the economic utility/loss interpretation and the brief require positive primitives; cases α≤0 or β≤0 are excluded
--   - reading: §3.1 uses the half-open effort interval → the closed interval [0,1/(2γr)] of Appendix A p. 43; reason: Appendix A specifies this boundary convention and it retains endpoint optima
--   - reading: τ is convex increasing → ConvexOn and MonotoneOn on the admissible effort interval; reason: increasing is read as nondecreasing, with no differentiability or strict-concavity requirement
--   - encoding: §5 states the active threshold branch and uses its overlapping-score-support profit formula → the feasible set explicitly imposes γp s≤1−θγr s≤1−γp s; reason: (13) describes actual probabilities only on this branch; for θ≥1 this also ensures both thresholds are in [0,1]
--   - reading: optimal learning decreases with θ; the proof uses a nonpositive cross derivative → nonincreasing comparison at strictly ordered θ, including boundary optima; reason: the source allows plateaus and does not specify uniqueness or a tie ordering at identical parameters
--   - generalization: the main text assumes the low-loss case βp ≤ αp + αr (p. 17) → no LowLoss hypothesis; reason: §5 fixes the branch cr = 1 − γr s, cp = 1 − θγr s directly and (13) and its comparison do not use the loss case; on LowLoss parameters the statement is exactly the source's
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 26, Theorem 4, eqs. (13)–(14); pp. 25–26 branch

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_GeneralFairness

namespace UnfairML.Coverage.Supplement

/-- Theorem 4, p. 26: all global maximizing efforts are ordered at strictly
ordered fairness parameters; identical parameters use the same chosen optimizer. -/
theorem theorem_4 (P : Params) (hS : P.Standing) (τ : ℝ → ℝ)
    (hτ : IsLearningCost P τ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 1 ≤ θ₁) (hθ : θ₁ < θ₂)
    (s₁ s₂ : ℝ) (h₁ : IsOptGeneral P τ θ₁ s₁) (h₂ : IsOptGeneral P τ θ₂ s₂) :
    s₂ ≤ s₁ := by sorry

end UnfairML.Coverage.Supplement
