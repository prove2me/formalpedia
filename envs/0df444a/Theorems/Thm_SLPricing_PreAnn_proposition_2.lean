-- Prove2me | Theorems.Thm_SLPricing_PreAnn_proposition_2
-- name    : SLPricing.PreAnn.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:48.400213+00:00
-- url     : https://prove2.me/theorems/ba55c38f-3bda-49a8-9c15-fe612421262f
-- title:
--   Proposition 2, p. 14 — with social learning, adoption inertia is never optimal, and for $\delta_c\ge\Delta(\gamma)$ the optimal plan has $p_1^*<p_2^*$
-- statement:
--   Assume social learning is present, $\gamma>0$. Write $\pi_p^*$ for the optimal pre-announced profit.
--
--   1. A plan inducing adoption inertia, $p_1-\delta_c p_2>1-\delta_c$, can never be optimal: in every purchasing equilibrium $B$ it earns
--   $$\pi_p(p_1,p_2;B)<\pi_p^* .$$
--   2. There is a threshold $\Delta(\gamma)\in[0,1]$ such that for every discount factor $\delta_c\in[\Delta(\gamma),1]$ (with $\sigma_p,\gamma,c$ fixed) an optimal plan exists, and every optimal plan $\{p_1^*,p_2^*\}$ satisfies
--   $$p_1^*<p_2^* .$$
--
--   So with social learning, patient consumers face an increasing price path, unlike the decreasing path of Proposition 1.
--
--   **Formalization Note** Part 2 asserts existence of an optimal plan so that "every optimal plan satisfies $p_1^*<p_2^*$" is not vacuous. The paper places $\Delta(\gamma)$ in $[0,1]$ (proof, p. 30); $\Delta=1$ is allowed, so the content of part 2 is at least the case $\delta_c=1$. The clause "any pre-announced price plan generates a unique equilibrium" is Lemma 2 and is not restated.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 2, p. 14; proof, pp. 29–30

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Proposition 2, p. 14 (proof pp. 29–30): with social learning (`γ > 0`),
(i) every plan inducing adoption inertia (`p₁ − δc p₂ > 1 − δc`) earns, in every equilibrium,
strictly less than the optimal pre-announced profit `π*_p`;
(ii) there is a threshold `Δ ∈ [0, 1]` such that for every `δc ∈ [Δ, 1]` an optimal plan exists
and every optimal plan satisfies `p₁* < p₂*`. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    (∀ (p₁ p₂ : ℝ) (B : Set ℝ), IsPreEq P p₁ p₂ B → 1 - P.δc < p₁ - P.δc * p₂ →
        ((preProfit P p₁ p₂ B : ℝ) : EReal) < preValue P) ∧
      ∃ Δ ∈ Icc (0 : ℝ) 1, ∀ d ∈ Icc Δ 1,
        (∃ p₁ p₂ : ℝ, IsOptimalPre (P.withδc d) p₁ p₂) ∧
        ∀ p₁ p₂ : ℝ, IsOptimalPre (P.withδc d) p₁ p₂ → p₁ < p₂ := by sorry

end SLPricing.PreAnn
