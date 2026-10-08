-- Prove2me | Theorems.Thm_TSTutorial_InfoRatio_sum_condMutualInfo_le_entropy
-- name    : TSTutorial.InfoRatio.sum_condMutualInfo_le_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:32.590659+00:00
-- url     : https://prove2.me/theorems/33707eea-1265-42ea-8fd8-059ea2057c71
-- title:
--   §8.1.2, p. 76 — the information gained about x* over T periods cannot exceed H(x*)
-- statement:
--   Consider the online decision problem with finite action set $\mathcal X$, finite outcome set $\mathcal Y$, prior $P$ on the parameter $\theta$, outcome kernel $q_\theta(\cdot\mid x)$ and optimal action $x^*=x^*(\theta)$, and let $\pi$ be any algorithm. For every horizon $T$,
--   $$\sum_{t=1}^T I\big(x^*;(x_t,y_t)\mid\mathbb H_{t-1}\big)\le H(x^*),$$
--   where $I(x^*;(x_t,y_t)\mid\mathbb H_{t-1})$ is the conditional mutual information between the optimal action and the period-$t$ action–outcome pair given the history $\mathbb H_{t-1}$ (averaged over $\mathbb H_{t-1}$), and $H(x^*)$ is the entropy of the prior distribution of $x^*$. Both are measured in nats.
--
--   The left side is the total expected information about $x^*$ acquired over $T$ periods; the statement says that it cannot exceed the initial uncertainty about $x^*$. This is the entropy budget that turns the Cauchy–Schwarz step of the proof of (8.8) into the bound $\sqrt{\bar\Gamma\,H(x^*)\,T}$.
--
--   **Formalization Note** The conditional mutual information is defined directly as an average of Kullback–Leibler divergences (a finite sum over histories, values of $x^*$ and observations, with $0\log 0=0$), not as a difference of unconditional mutual informations, so the chain rule is part of what is to be proved. $\mathcal X$ and $\mathcal Y$ are finite. Periods are 0-based in Lean: Lean period $s$ is tutorial period $t=s+1$.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 76, §8.1.2, sentence after the display following (8.8) (citing Russo and Van Roy 2016)

import Mathlib
import Definitions.Def_TSTutorial_InfoRatio_Setting

namespace TSTutorial.InfoRatio

theorem sum_condMutualInfo_le_entropy {X Y Θ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [MeasurableSpace Θ] (M : Model X Y Θ) (π : Policy X Y) (hπ : IsPolicy π) (T : ℕ) :
    ∑ s : Fin T, condMutualInfo M π s ≤ entropyStar M := by sorry

end TSTutorial.InfoRatio
