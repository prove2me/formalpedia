-- Prove2me | Theorems.Thm_UnfairML_Coverage_Supplement_theorem_8
-- name    : UnfairML.Coverage.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:39:30.591488+00:00
-- url     : https://prove2.me/theorems/1ffd8e79-33ec-4eeb-91d5-b84f44e80b2e
-- title:
--   Theorem 8 (corrected: positive utilities) — ET learning is nondecreasing in protected default with fixed expected loss
-- statement:
--   Fix $\beta,d_r,c,\gamma_p,\gamma_r$ with $c>0$, and fix the same convex nondecreasing learning cost $\tau$ throughout. For two protected default proportions $u_1<u_2$, recompute the utility and group payoffs using (39)–(40):
--   $$\alpha(u)=\frac{\beta(u+d_r)-2c}{2-u-d_r},\quad
--   \alpha_p(u)=\alpha(u)(1-u),\quad\alpha_r(u)=\alpha(u)(1-d_r),\quad\beta_p(u)=\beta u,\quad\beta_r=\beta d_r.$$
--   At each $u_i$, require positive utility and loss, $0<d_r<u_i<1$, $\alpha_r(u_i)\le\beta_r$, $0<\gamma_p<\gamma_r$ and the active low-loss branch $\beta_p(u_i)\le\alpha_p(u_i)+\alpha_r(u_i)$. Let $s_i$ be any attained global maximum of the actual reduced ET objective (41) at $u_i$ over $[0,1/(2\gamma_r)]$. Then
--   $$s_1\le s_2.$$
--   Both groups' expected revenues change with $u$. The cost condition need only be imposed once, since the effort domain depends solely on the fixed $\gamma_r$. The statement retains boundary optima and makes no claim of strict movement on every boundary plateau. At the same default proportion the same selected optimizer gives equality.
--
--   Differences from the source:
--   - correction: Table 1 calls α and β utility and dis-utility without explicitly imposing positivity → α>0 and β>0 through the published Standing predicate; reason: the economic utility/loss interpretation and the brief require positive primitives; cases α≤0 or β≤0 are excluded
--   - reading: §3.1 uses the half-open effort interval → the closed interval [0,1/(2γr)] of Appendix A p. 43; reason: Appendix A specifies this boundary convention and it retains endpoint optima
--   - reading: τ is convex increasing → ConvexOn and MonotoneOn on the admissible effort interval; reason: increasing is read as nondecreasing, with no differentiability or strict-concavity requirement
--   - encoding: (39)–(40) fix positive c and determine α as the protected default varies → responseParams recomputes both αp and αr at each u and assumes the standing and active-branch conditions at both endpoints; reason: (41) is the low-loss ET objective; the two endpoints must be admissible source models and neither α nor αr is held fixed
--   - reading: effort increases with dp → nondecreasing comparison at strictly ordered default rates, with the same optimizer at identical rates; reason: boundary plateaus remain possible and the source specifies no uniqueness or tie ordering
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 39, Theorem 8; p. 38, eqs. (39)–(46)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_Response

namespace UnfairML.Coverage.Supplement

/-- Theorem 8, p. 39: compare globally optimal efforts at distinct protected
default rates with all fixed data and the same arbitrary convex increasing cost. -/
theorem theorem_8 (β dr c γp γr : ℝ) (hc : 0 < c) (τ : ℝ → ℝ)
    (u₁ u₂ : ℝ) (hu : u₁ < u₂)
    (hS₁ : (responseParams β dr c γp γr u₁).Standing)
    (hS₂ : (responseParams β dr c γp γr u₂).Standing)
    (hL₁ : (responseParams β dr c γp γr u₁).LowLoss)
    (hL₂ : (responseParams β dr c γp γr u₂).LowLoss)
    (hτ : IsLearningCost (responseParams β dr c γp γr u₁) τ)
    (s₁ s₂ : ℝ)
    (h₁ : IsOptResponse β dr c γp γr τ u₁ s₁)
    (h₂ : IsOptResponse β dr c γp γr τ u₂ s₂) :
    s₁ ≤ s₂ := by sorry

end UnfairML.Coverage.Supplement
