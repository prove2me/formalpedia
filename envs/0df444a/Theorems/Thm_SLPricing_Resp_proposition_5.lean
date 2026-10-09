-- Prove2me | Theorems.Thm_SLPricing_Resp_proposition_5
-- name    : SLPricing.Resp.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:40.732751+00:00
-- url     : https://prove2.me/theorems/60a2fe7c-7662-4d0b-a221-f010bf986c71
-- title:
--   Proposition 5, p. 22 — with SL, adoption inertia is never optimal, and the second-period price follows (6) at $\bar x=\zeta(p_1^*)$
-- statement:
--   Consider responsive pricing with social learning ($\gamma>0$), and let $\pi_r^*$ be the optimal expected profit. Write $\bar p=\frac{2-\delta_c(1-c)}{2}$.
--
--   1. For every first-period price $p_1>\bar p$ (which induces adoption inertia) and every equilibrium after it, the firm's expected profit is strictly less than $\pi_r^*$. Consequently every optimal first-period price satisfies
--   $$p_1^*\le\frac{2-\delta_c(1-c)}{2}.$$
--   2. In every equilibrium whose set of first-period buyers equals $[\zeta,1]$ up to a null set, with $\zeta\in(0,1]$, the second-period price at the realized posterior mean $q_u$ is
--   $$p_2^*=\frac{q_u+c+\zeta}{2}\ \text{ if } c-\zeta<q_u\le c+\zeta,\qquad p_2^*=q_u\ \text{ if } q_u>c+\zeta,$$
--   and when $q_u\le c-\zeta$ no second-period sale takes place (the paper's $p_2^*=c$).
--
--   Applied with $\zeta=\zeta(p_1^*)$ of Lemma 4, part 2 is the paper's optimal second-period price. The proposition shows that the equilibrium price path is stochastic and never starts with an introductory price that makes everybody wait.
--
--   **Formalization Note** Part 2 is stated for every equilibrium with a threshold, not only after the optimal $p_1^*$. The header "any first-period price generates a unique equilibrium" is the content of Lemma 4 (buyer set) and Lemma 3 (second-period price), and is not restated. The printed proof of part 1 compares inertia with the price $p_1=(1+c)/2$; at $\delta_c=1$ that comparison gives equality, so the statement at $\delta_c=1$ needs a different witness. The statement is kept as printed.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 5, p. 22 (proof p. 33)

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
import Definitions.Def_SLPricing_Resp_P2Star
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Proposition 5, p. 22 (proof p. 33): with social learning (`γ > 0`) under responsive pricing,
(i) every equilibrium after a first-period price `p₁ > (2 − δc(1 − c))/2` (adoption inertia)
earns strictly less than the optimal expected profit `π*_r`, so every optimal first-period price
satisfies `p∗₁ ≤ (2 − δc(1 − c))/2`;
(ii) in every equilibrium whose first-period buyers are the types `[ζ, 1]` (up to a null set),
`ζ ∈ (0, 1]`, the second-period price is `p∗₂(q_u, ζ)` of (6) whenever `q_u > c − ζ`, and no
second-period sale occurs when `q_u ≤ c − ζ`. -/
theorem proposition_5 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    (∀ p₁ B s, IsRespEq P p₁ B s → (2 - P.δc * (1 - P.c)) / 2 < p₁ →
      ((respProfit P p₁ B s : ℝ) : EReal) < respValue P) ∧
    (∀ p₁, IsOptimalResp P p₁ → p₁ ≤ (2 - P.δc * (1 - P.c)) / 2) ∧
    (∀ p₁ B s ζ, IsRespEq P p₁ B s → ζ ∈ Ioc (0 : ℝ) 1 → B =ᵐ[volume] Icc ζ 1 →
      (∀ q, P.c - ζ < q → s q = p2Star P.c q ζ) ∧
      (∀ q, q ≤ P.c - ζ → lateMass B (s q) q = 0)) := by sorry

end SLPricing.Resp
