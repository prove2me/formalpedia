-- Prove2me | Theorems.Thm_SLPricing_Compare_theta_eq_p1_myopic
-- name    : SLPricing.Compare.theta_eq_p1_myopic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:50.584186+00:00
-- url     : https://prove2.me/theorems/3f162565-b0d5-46af-b9f4-662577528a1f
-- title:
--   Proof of Example 1, p. 30 — for $\delta_c = 0$ the pre-announced purchasing threshold is $\theta(p_1,p_2) = p_1$
-- statement:
--   Consider the model of the mission with myopic consumers, $\delta_c = 0$, and any SL parameter $\gamma \ge 0$. Under pre-announced pricing, fix a price plan $\{p_1, p_2\}$ with $p_1 \in [0,1]$. Then the set of types
--   $$B = [p_1, 1]$$
--   is a purchasing equilibrium, and every purchasing equilibrium $B'$ coincides with $[p_1,1]$ up to a Lebesgue-null set. In the paper's words, the first-period purchasing threshold is $\theta(p_1,p_2) = p_1$ for every plan.
--
--   This is the starting point of the comparison at $\delta_c = 0$: myopic consumers buy early exactly when their first-period utility is non-negative, independently of $p_2$ and of what they will learn.
--
--   **Formalization Note** The hypothesis $p_1 \in [0,1]$ is added: for $p_1 > 1$ no type buys early and "$\theta = p_1$" has no meaning. Uniqueness is up to null sets because the indifferent type $x = p_1$ may go either way.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Appendix A, proof of Example 1, p. 30

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Appendix A, proof of Example 1, p. 30: for `δc = 0` the first-period purchasing threshold
under pre-announced pricing is `θ(p₁, p₂) = p₁` for every plan with `p₁ ∈ [0, 1]`: `[p₁, 1]` is a
purchasing equilibrium, and every purchasing equilibrium equals it up to a null set. -/
theorem theta_eq_p1_myopic (P : Params) (hP : P.Standing) (hδ : P.δc = 0)
    (p₁ p₂ : ℝ) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) :
    IsPreEq P p₁ p₂ (Icc p₁ 1) ∧
      ∀ B : Set ℝ, IsPreEq P p₁ p₂ B → B =ᵐ[volume] Icc p₁ 1 := by sorry

end SLPricing.Compare
