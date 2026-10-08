-- Prove2me | Theorems.Thm_TSTutorial_InfoRatio_regret_le_sqrt_infoRatio_entropy
-- name    : TSTutorial.InfoRatio.regret_le_sqrt_infoRatio_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:44.404156+00:00
-- url     : https://prove2.me/theorems/e38d28f4-c730-45f1-99fb-879507ec3f5c
-- title:
--   (8.8), p. 76 — 𝔼[Regret(T)] ≤ √(Γ̄ H(x*) T) for any model and algorithm
-- statement:
--   Consider any online decision problem with finite action set $\mathcal X$, finite outcome set $\mathcal Y$, a prior $P$ on the parameter $\theta$ (in a general measurable space), outcome kernel $q_\theta(\cdot\mid x)$, known reward $r$, mean reward $\mu(x,\theta)$ and optimal action $x^*=x^*(\theta)\in\arg\max_x\mu(x,\theta)$, and any algorithm $\pi$. Fix a horizon $T$ and let $\bar\Gamma\ge0$ bound the information ratio of every period:
--   $$\big(\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)]\big)^2\le\bar\Gamma\; I\big(x^*;(x_t,y_t)\mid\mathbb H_{t-1}\big)\qquad(t=1,\dots,T).$$
--   Then
--   $$\mathbb E[\mathrm{Regret}(T)]\le\sqrt{\bar\Gamma\,H(x^*)\,T},$$
--   where $H(x^*)$ is the entropy of the prior distribution of the optimal action.
--
--   When every conditional mutual information is positive, the smallest admissible $\bar\Gamma$ is $\max_{t\in\{1,\dots,T\}}\Gamma_t$ with $\Gamma_t$ the information ratio (8.7), and the statement is (8.8) as printed. The bound applies to every model and every algorithm; its feature is the dependence on the initial uncertainty $H(x^*)$ about the optimal action rather than on the number of actions.
--
--   **Formalization Note** (8.7) divides by the conditional mutual information, which can be $0$; the bound is therefore stated for every $\bar\Gamma\ge0$ satisfying $(\text{expected regret})^2\le\bar\Gamma\cdot I$ in every period, which is equivalent to $\bar\Gamma\ge\max_t\Gamma_t$ when all the mutual informations are positive and is the sense in which "$\Gamma_t\le\bar\Gamma$" is used on p. 76. The literal form with $\bar\Gamma=\max_t\Gamma_t$ is the companion theorem `regret_le_sqrt_maxInfoRatio_entropy`. The tutorial's model allows infinite action sets and general outcomes; here both are finite, while $\theta$ is general. Mutual information and entropy both use natural logarithms. The algorithm is a behavioural policy (a probability vector over actions for each history), and periods are 0-based in Lean.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 76, (8.8), with (8.7) on p. 75

import Mathlib
import Definitions.Def_TSTutorial_InfoRatio_Setting

namespace TSTutorial.InfoRatio

theorem regret_le_sqrt_infoRatio_entropy {X Y Θ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [MeasurableSpace Θ] (M : Model X Y Θ) (π : Policy X Y) (hπ : IsPolicy π) (T : ℕ)
    (Γ : ℝ) (hΓ_nonneg : 0 ≤ Γ)
    (hΓ : ∀ s : Fin T, periodRegret M π s ^ 2 ≤ Γ * condMutualInfo M π s) :
    expRegret M π T ≤ Real.sqrt (Γ * entropyStar M * T) := by sorry

end TSTutorial.InfoRatio
