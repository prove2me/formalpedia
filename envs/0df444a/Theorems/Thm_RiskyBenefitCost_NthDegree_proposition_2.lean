-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_proposition_2
-- name    : RiskyBenefitCost.NthDegree.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:17.693538+00:00
-- url     : https://prove2.me/theorems/bdd58040-2c1b-43dc-8d70-e769f56f1433
-- title:
--   Proposition 2, p. 3628 (PDF 5) — Nth-degree risk increases lower risk taking for a risky benefit, and for a risky cost iff N is even
-- statement:
--   Consider the linear-payoff problem
--   $$\max_{b\in B}\ \mathbb E\,U\big(f(b)(\tilde X-x_0)+z_0\big)$$
--   with $N\ge1$, $\tilde X\ge0$ taking values in $[\underline x,\bar x]$ ($0\le\underline x<\bar x$), $z_0\ge0$, $B\subset\mathbb R$ compact, $f$ continuous on $B$, and $U$ increasing and $(N+1)$ times continuously differentiable. Let $D$ be an interval containing every payoff $f(b)(X-x_0)+z_0$ ($b\in B$, $X\in[\underline x,\bar x]$) — the relevant domain of the utility function. Suppose that on $D$ the decision maker is $N$th- and $(N+1)$th-degree risk averse,
--   $$(-1)^{N+1}U^{(N)}>0,\qquad (-1)^{N+2}U^{(N+1)}\ge0,$$
--   with relative $(N+1)$th-degree risk aversion $r_{N+1}(z)=-zU^{(N+1)}(z)/U^{(N)}(z)$ below $N$. Let $\tilde X_2$ be an $N$th-degree risk increase over $\tilde X_1$, and let $B^*_i$ be the set of maximizers under $\tilde X_i$. Then, in the strong set order:
--   1. For a risky benefit, $B_2^*\le_S B_1^*$ in the risk-taking problem and $B_2^*\ge_S B_1^*$ in the risk-mitigation problem.
--   2. For a risky cost, if $N$ is even, $B_2^*\le_S B_1^*$ in the risk-taking problem and $B_2^*\ge_S B_1^*$ in the risk-mitigation problem; if $N$ is odd, the orderings are reversed.
--
--   The result says that an increase in $N$th-degree risk of a risky benefit always reduces exposure to risk, while for a risky cost the direction depends on the parity of $N$: it is "a question of the right order".
--
--   **Formalization Note.** Random variables are their laws, probability measures concentrated on $[\underline x,\bar x]$. $D\ge_S D'$ means: for $d\in D$, $d'\in D'$, $\max\{d,d'\}\in D$ and $\min\{d,d'\}\in D'$; $B_2^*\le_S B_1^*$ is `InducedSetOrder B₂ B₁`. $N$th-degree risk aversion is taken strictly because Definition 4 defines $r_{N+1}$ only where $(-1)^{N+1}U^{(N)}>0$; "below $N$" is strict. Added hypothesis: $z_0\ge0$, which the paper's sign argument for display (8) uses silently. $U$ is smooth on all of $\mathbb R$ and the risk attitudes are imposed only on $D$. The trade-off condition of footnote 3 (mass above and below $x_0$) is not assumed; it is not a hypothesis of Proposition 2. Nonemptiness of $B_i^*$ is not assumed (it is a separate milestone).
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3628 (PDF 5), Proposition 2

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree
open MeasureTheory ProbabilityTheory

theorem proposition_2 (N : ℕ) (hN : 1 ≤ N) (xl xu x0 z0 : ℝ) (hxl : 0 ≤ xl) (hlt : xl < xu)
    (hz0 : 0 ≤ z0)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : μ₁ (Set.Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Set.Icc xl xu)ᶜ = 0)
    (B : Set ℝ) (hB : IsCompact B) (f : ℝ → ℝ) (hf : ContinuousOn f B)
    (U : ℝ → ℝ) (hU : ContDiff ℝ (N + 1) U) (hUmono : Monotone U)
    (D : Set ℝ) (hD : D.OrdConnected)
    (hpay : ∀ b ∈ B, ∀ X ∈ Set.Icc xl xu, f b * (X - x0) + z0 ∈ D)
    (hRA_N : ∀ z ∈ D, 0 < (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U z)
    (hRA_N1 : NthDegreeRiskAverseOn (N + 1) U D)
    (hrel : ∀ z ∈ D, relRiskAversion N U z < N)
    (hinc : IsNthDegreeRiskIncrease N xl xu μ₁ μ₂) :
    (RiskTakingBenefit f B →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁))) ∧
    (RiskMitigationBenefit f B →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂))) ∧
    (RiskTakingCost f B →
      (Even N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁))) ∧
      (Odd N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂)))) ∧
    (RiskMitigationCost f B →
      (Even N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂))) ∧
      (Odd N → Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁)))) := by sorry

end RiskyBenefitCost.NthDegree
