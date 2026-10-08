-- Prove2me | Theorems.Thm_TSTutorial_KnownStandard_case_first_action_two
-- name    : TSTutorial.KnownStandard.case_first_action_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:44.36604+00:00
-- url     : https://prove2.me/theorems/76e39253-66b0-4820-97f1-7925c45fe385
-- title:
--   Example 8.1, p. 79 — if x₁ = 2 for all p₀ > 0, then x_t = 2 for all t and 𝔼[Regret(T)] = T·(1 − p₀)/4
-- statement:
--   Consider the known-standard problem of Example 8.1: two actions, $\theta\sim\mathrm{Bernoulli}(p_0)$, action $1$ paying $\mathrm{Bernoulli}(1/2)$, action $2$ paying $\mathrm{Bernoulli}(3/4)$ if $\theta=1$ and $\mathrm{Bernoulli}(1/4)$ if $\theta=0$. Let $f$ be a stationary deterministic strategy, $x_t=f(p_{t-1})$, where $p_{t-1}$ is the posterior probability that $\theta=1$ given $\mathbb H_{t-1}$.
--
--   Suppose that $f(p)=2$ for every $p\in(0,1]$, i.e. the strategy selects $x_1=2$ for every prior $p_0>0$. Then for every prior $p_0\in(0,1]$ and every horizon $T$:
--
--   1. on every history $\mathbb H_T$ of positive probability, $x_t=2$ for every $t=1,\dots,T$;
--   2. the expected cumulative regret is exactly
--   $$\mathbb E[\mathrm{Regret}(T)]=\frac{1-p_0}{4}\,T .$$
--
--   The posterior stays in $(0,1]$, so the strategy keeps playing action $2$, which loses $1/2-1/4=1/4$ per period when $\theta=0$. This is the second case of the argument of Example 8.1; for $p_0<1$ the regret grows linearly in $T$.
--
--   **Formalization Note** Paper actions $1,2$ are Lean `0, 1 : Fin 2`. "For all $p_0>0$" is read as for all $p_0\in(0,1]$, the values a prior probability can take. "A history of positive probability" is $\sum_\theta \mathrm{prior}(\theta)\,\mathbb P_\theta(\mathbb H_T=h)>0$.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 79, §8.1.3, Example 8.1 (second paragraph, fifth sentence)

import Mathlib
import Definitions.Def_TSTutorial_KnownStandard_Setting

namespace TSTutorial.KnownStandard
theorem case_first_action_two (f : Strategy) (hf : ∀ p : ℝ, 0 < p → p ≤ 1 → f p = 1)
    (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1) (T : ℕ) :
    (∀ h : Hist T, 0 < ∑ θ : Bool, prior p₀ θ * lawGiven f p₀ T θ h →
      ∀ s : Fin T, (h s).1 = 1) ∧
    expRegret f p₀ T = T * ((1 - p₀) / 4) := by sorry
end TSTutorial.KnownStandard
