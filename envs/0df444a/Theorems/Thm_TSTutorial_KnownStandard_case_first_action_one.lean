-- Prove2me | Theorems.Thm_TSTutorial_KnownStandard_case_first_action_one
-- name    : TSTutorial.KnownStandard.case_first_action_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:33.015151+00:00
-- url     : https://prove2.me/theorems/df201cf4-8d52-43f2-8218-2fbae002b0b7
-- title:
--   Example 8.1, p. 79 — if x₁ = 1 for some p₀ > 0, then p_t = p₀, x_t = 1 for all t and 𝔼[Regret(T)] = T·p₀/4
-- statement:
--   Consider the known-standard problem of Example 8.1: two actions, $\theta\sim\mathrm{Bernoulli}(p_0)$, action $1$ paying $\mathrm{Bernoulli}(1/2)$, action $2$ paying $\mathrm{Bernoulli}(3/4)$ if $\theta=1$ and $\mathrm{Bernoulli}(1/4)$ if $\theta=0$. Let $f$ be a stationary deterministic strategy, $x_t=f(p_{t-1})$, where $p_{t-1}$ is the posterior probability that $\theta=1$ given $\mathbb H_{t-1}$.
--
--   Suppose $0<p_0\le 1$ and $f(p_0)=1$, i.e. the strategy selects $x_1=1$. Then for every horizon $T$:
--
--   1. on every history $\mathbb H_T$ of positive probability, $p_t=p_0$ for every $t=0,\dots,T$ and $x_t=1$ for every $t=1,\dots,T$;
--   2. the expected cumulative regret is exactly
--   $$\mathbb E[\mathrm{Regret}(T)]=\frac{p_0}{4}\,T .$$
--
--   Since action $1$'s reward is uninformative about $\theta$, the posterior never moves and the strategy keeps playing action $1$, which loses $3/4-1/2=1/4$ per period when $\theta=1$. This is the first case of the argument of Example 8.1; the regret grows linearly in $T$.
--
--   **Formalization Note** Paper actions $1,2$ are Lean `0, 1 : Fin 2`. "A history of positive probability" is $\sum_\theta \mathrm{prior}(\theta)\,\mathbb P_\theta(\mathbb H_T=h)>0$. The case $p_0=1$ is included (the text only requires $p_0>0$).
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 79, §8.1.3, Example 8.1 (second paragraph, third and fourth sentences)

import Mathlib
import Definitions.Def_TSTutorial_KnownStandard_Setting

namespace TSTutorial.KnownStandard
theorem case_first_action_one (f : Strategy) (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hf : f p₀ = 0) (T : ℕ) :
    (∀ h : Hist T, 0 < ∑ θ : Bool, prior p₀ θ * lawGiven f p₀ T θ h →
      post p₀ h = p₀ ∧ ∀ s : Fin T, post p₀ (histPrefix h s) = p₀ ∧ (h s).1 = 0) ∧
    expRegret f p₀ T = T * (p₀ / 4) := by sorry
end TSTutorial.KnownStandard
