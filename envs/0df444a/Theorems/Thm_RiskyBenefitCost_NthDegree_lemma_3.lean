-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_lemma_3
-- name    : RiskyBenefitCost.NthDegree.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:14.071001+00:00
-- url     : https://prove2.me/theorems/11bf5fb2-428f-4078-9b04-132caaf4c278
-- title:
--   Lemma 3, p. 3627 (PDF 4) — B∗₂ ≥S B∗₁ (≤S) if the sign-adjusted Nth derivative (5) is increasing (decreasing) in b
-- statement:
--   Consider the linear-payoff problem $\max_{b\in B}\mathbb E\,U\big(f(b)(\tilde X-x_0)+z_0\big)$ with $B\subset\mathbb R$ compact, $f$ continuous on $B$, $U$ increasing and $(N+1)$ times continuously differentiable, $N\ge1$, and $\tilde X\ge0$ with values in $[\underline x,\bar x]$, $\underline x<\bar x$. Let $\tilde X_2$ be an $N$th-degree risk increase over $\tilde X_1$, and let $B_i^*$ be the maximizer set under $\tilde X_i$.
--
--   1. If for every $X\in[\underline x,\bar x]$ the function
--   $$b\longmapsto (-1)^N f(b)^N\,U^{(N)}\big(f(b)(X-x_0)+z_0\big)\qquad(5)$$
--   is increasing on $B$, then $B_2^*\ge_S B_1^*$.
--   2. If it is decreasing on $B$ for every such $X$, then $B_2^*\le_S B_1^*$.
--
--   Here $D\ge_S D'$ is the strong set order: for all $d\in D$, $d'\in D'$, $\max\{d,d'\}\in D$ and $\min\{d,d'\}\in D'$.
--
--   Lemma 3 reduces the comparative statics of a risk increase to a pointwise monotonicity property of (5); Proposition 2 is proved by checking that property in each problem class.
--
--   **Formalization Note.** The page's "for all $X$" is read as all $X$ in the support $[\underline x,\bar x]$. $B_2^*\ge_S B_1^*$ is `InducedSetOrder B₁ B₂` (the first argument receives the minima). "Increasing/decreasing" are weak (`MonotoneOn`/`AntitoneOn`). No nonemptiness of $B_i^*$ is assumed.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3627 (PDF 4), Lemma 3 and display (5)

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree
open MeasureTheory ProbabilityTheory

theorem lemma_3 (N : ℕ) (hN : 1 ≤ N) (xl xu x0 z0 : ℝ) (hxl : 0 ≤ xl) (hlt : xl < xu)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : μ₁ (Set.Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Set.Icc xl xu)ᶜ = 0)
    (B : Set ℝ) (hB : IsCompact B) (f : ℝ → ℝ) (hf : ContinuousOn f B)
    (U : ℝ → ℝ) (hU : ContDiff ℝ (N + 1) U) (hUmono : Monotone U)
    (hinc : IsNthDegreeRiskIncrease N xl xu μ₁ μ₂) :
    ((∀ X ∈ Set.Icc xl xu, MonotoneOn (fun b => signAdj N U f x0 z0 X b) B) →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₁)) (argmaxSet B (EU U f x0 z0 μ₂))) ∧
    ((∀ X ∈ Set.Icc xl xu, AntitoneOn (fun b => signAdj N U f x0 z0 X b) B) →
      Supermodularity.Lattices.InducedSetOrder
        (argmaxSet B (EU U f x0 z0 μ₂)) (argmaxSet B (EU U f x0 z0 μ₁))) := by sorry

end RiskyBenefitCost.NthDegree
