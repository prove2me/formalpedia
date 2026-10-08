-- Prove2me | Theorems.Thm_TsallisINF_Half_lemma_15
-- name    : TsallisINF.Half.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:00.663455+00:00
-- url     : https://prove2.me/theorems/4b5e5e5b-3fbd-46fe-8be4-881e3dedf748
-- title:
--   Lemma 15: a reciprocal-power tail sum
-- statement:
--   Let $b,c>0$ and natural numbers $T_0<T$ satisfy $b\sqrt{T_0}>c$. Then
--
--   $$
--   \sum_{t=T_0+1}^{T}\frac1{bt^{3/2}-ct}\le\frac2{b\sqrt{T_0}-c}.
--   $$
--
--   The denominator condition makes every summand well defined and positive. The estimate is used in the late-round part of Theorem 1's self-bounding analysis.
--
--   **Formalization Note** Real powers represent $t^{3/2}$. The strict denominator condition excludes $T_0=0$ automatically.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 32, Lemma 15

import Mathlib

namespace TsallisINF.Half

/-- Lemma 15: a bound on a finite tail sum used in Theorem 1. -/
theorem lemma_15 (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (T₀ T : ℕ) (hT : T₀ < T) (hden : c < b * Real.sqrt (T₀ : ℝ)) :
    (∑ t ∈ Finset.Icc (T₀ + 1) T,
      1 / (b * (t : ℝ) ^ (3 / 2 : ℝ) - c * (t : ℝ))) ≤
        2 / (b * Real.sqrt (T₀ : ℝ) - c) := by sorry

end TsallisINF.Half
