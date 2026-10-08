-- Prove2me | Theorems.Thm_TSTutorial_InfoRatio_expRegret_eq_sum_periodRegret
-- name    : TSTutorial.InfoRatio.expRegret_eq_sum_periodRegret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:21.973428+00:00
-- url     : https://prove2.me/theorems/3fc25ddf-3c10-40b5-85aa-47f2a787aef9
-- title:
--   §8.1.2, p. 76, display after (8.8) — 𝔼[Regret(T)] is the sum of the expected per-period regrets
-- statement:
--   Consider the online decision problem with finite action set $\mathcal X$, finite outcome set $\mathcal Y$, prior $P$ on the parameter $\theta$, outcome kernel $q_\theta(\cdot\mid x)$, mean reward $\mu(x,\theta)$ and optimal action $x^*=x^*(\theta)$, and let $\pi$ be any algorithm (an adaptive, possibly randomized rule selecting each action from the history). Then for every horizon $T$,
--   $$\mathbb E[\mathrm{Regret}(T)]=\sum_{t=1}^T\mathbb E\big[\mu(x^*,\theta)-\mu(x_t,\theta)\big].$$
--   On the left the expectation is under the joint law of $\theta$ and the full history $\mathbb H_T$; in the $t$-th summand on the right it is under the joint law of $\theta$ and the history $\mathbb H_t$ up to period $t$.
--
--   This is the first step of the proof of (8.8): it reduces the cumulative regret to per-period regrets, each of which is compared with the information gained in that period.
--
--   **Formalization Note** The two sides are different expressions: the left integrates over histories of length $T$, the $t$-th term on the right over histories of length $t$, so the identity says that later periods integrate out (the algorithm's action probabilities and the outcome probabilities each sum to $1$). Periods are 0-based in Lean: the summand for Lean period $s$ is tutorial period $t=s+1$. The setting is finite $\mathcal X$ and $\mathcal Y$, as in the definition file.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 76, §8.1.2, first equality of the display after (8.8); regret as defined on p. 71

import Mathlib
import Definitions.Def_TSTutorial_InfoRatio_Setting

namespace TSTutorial.InfoRatio

theorem expRegret_eq_sum_periodRegret {X Y Θ : Type} [Fintype X] [Fintype Y]
    [MeasurableSpace Θ] (M : Model X Y Θ) (π : Policy X Y) (hπ : IsPolicy π) (T : ℕ) :
    expRegret M π T = ∑ s : Fin T, periodRegret M π s := by sorry

end TSTutorial.InfoRatio
