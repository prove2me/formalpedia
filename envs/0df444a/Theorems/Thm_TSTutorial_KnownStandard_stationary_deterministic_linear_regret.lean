-- Prove2me | Theorems.Thm_TSTutorial_KnownStandard_stationary_deterministic_linear_regret
-- name    : TSTutorial.KnownStandard.stationary_deterministic_linear_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:51.214522+00:00
-- url     : https://prove2.me/theorems/dfd866d6-9f82-40b7-a25d-0e136a54202d
-- title:
--   Example 8.1, p. 79 — for every stationary deterministic strategy some prior p₀ makes 𝔼[Regret(T)] grow linearly
-- statement:
--   Consider the known-standard problem of Example 8.1 (p. 79): two actions $\mathcal X=\{1,2\}$, a parameter $\theta\sim\mathrm{Bernoulli}(p_0)$, action $1$ paying $\mathrm{Bernoulli}(1/2)$ and action $2$ paying $\mathrm{Bernoulli}(3/4)$ if $\theta=1$ and $\mathrm{Bernoulli}(1/4)$ if $\theta=0$. A stationary deterministic strategy chooses $x_t=f(p_{t-1})$ for one fixed function $f$, where $p_{t-1}=\mathbb P(\theta=1\mid\mathbb H_{t-1})$ is the Bayes posterior (4.2).
--
--   **Claim.** For every stationary deterministic strategy $f$ there exist a prior probability $p_0\in(0,1]$ and a constant $c>0$ such that for every horizon $T$
--   $$\mathbb E[\mathrm{Regret}(T)]\;\ge\; c\,T,$$
--   where $\mathbb E[\mathrm{Regret}(T)]=\mathbb E\big[\sum_{t=1}^T(\mu(x^*,\theta)-\mu(x_t,\theta))\big]$ is the expected cumulative regret under the prior $\mathrm{Bernoulli}(p_0)$ (p. 71).
--
--   The example shows that sublinear Bayesian regret bounds, such as those for Thompson sampling, cannot be achieved by a strategy that is both stationary and deterministic: a stationary strategy must randomize, or a deterministic one must depend on time, as UCB algorithms do.
--
--   **Formalization Note** Paper actions $1,2$ are Lean `0, 1 : Fin 2`, and $\theta=1$ is `true`. The quantifiers are in the paper's order: for every $f$ there is a $p_0$ (the prior may depend on the strategy). "Grows linearly with time" is read as a linear lower bound $cT$ with $c>0$ for all $T$; an upper bound $T/4$ holds for every strategy and is not part of the claim. $p_0>0$ as in the text, and $p_0\le 1$ because it is a probability.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 79, §8.1.3, Example 8.1 (sixth sentence: "It follows that, for any deterministic stationary strategy, there exists a prior probability p₀ such that expected cumulative regret grows linearly with time.")

import Mathlib
import Definitions.Def_TSTutorial_KnownStandard_Setting

namespace TSTutorial.KnownStandard
theorem stationary_deterministic_linear_regret (f : Strategy) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, c * T ≤ expRegret f p₀ T := by sorry
end TSTutorial.KnownStandard
