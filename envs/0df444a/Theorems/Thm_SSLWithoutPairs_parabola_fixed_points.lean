-- Prove2me | Theorems.Thm_SSLWithoutPairs_parabola_fixed_points
-- name    : SSLWithoutPairs.parabola_fixed_points
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:42:05.31875+00:00
-- url     : https://prove2.me/theorems/40397c70-9070-4b80-9ad9-4c8a1ad28f0a
-- title:
--   Section 3.2: fixed points of eq. (16) and their basins of attraction
-- statement:
--   Fix $\tau>0$, $\eta>0$ and $\sigma\in\mathbb R$, and consider the predictor mode on the invariant parabola,
--
--   $$\dot p_j=p_j^2[\tau-(1+\sigma^2)p_j]-\eta p_j.$$
--
--   Let $p^*_{j\pm}=\dfrac{\tau\pm\sqrt{\tau^2-4\eta(1+\sigma^2)}}{2(1+\sigma^2)}$.
--
--   1. If $\eta\le\dfrac{\tau^2}{4(1+\sigma^2)}$, the fixed points are exactly $p^*_{j0}=0$, $p^*_{j-}$ and $p^*_{j+}$, with $0<p^*_{j-}\le p^*_{j+}$. Every solution with $p_j(0)<p^*_{j-}$ tends to $0$, and every solution with $p_j(0)>p^*_{j-}$ tends to $p^*_{j+}$.
--   2. If $\eta>\dfrac{\tau^2}{4(1+\sigma^2)}$, the only fixed point is $0$ and every solution tends to $0$: collapse is unavoidable.
--
--   **Formalization Note** Stability is stated through the basins of attraction that the paper gives. At $\eta=\tau^2/(4(1+\sigma^2))$, which the paper includes, $p^*_{j-}=p^*_{j+}$, so there are only two fixed points. The statement keeps the paper's range and describes the fixed-point set as $\{0,p^*_{j-},p^*_{j+}\}$.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3.2, eq. (16) and the display following it, p. 6

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem parabola_fixed_points (σ η τ : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    (η ≤ τ ^ 2 / (4 * (1 + σ ^ 2)) →
      {p : ℝ | parabolaFlowP σ η τ p = 0} = {0, fixedPointMinus σ η τ, fixedPointPlus σ η τ} ∧
      0 < fixedPointMinus σ η τ ∧ fixedPointMinus σ η τ ≤ fixedPointPlus σ η τ ∧
      ∀ p : ℝ → ℝ,
        (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (parabolaFlowP σ η τ (p t)) (Set.Ici 0) t) →
        (p 0 < fixedPointMinus σ η τ → Tendsto p atTop (𝓝 0)) ∧
        (fixedPointMinus σ η τ < p 0 → Tendsto p atTop (𝓝 (fixedPointPlus σ η τ)))) ∧
    (τ ^ 2 / (4 * (1 + σ ^ 2)) < η →
      {p : ℝ | parabolaFlowP σ η τ p = 0} = {0} ∧
      ∀ p : ℝ → ℝ,
        (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (parabolaFlowP σ η τ (p t)) (Set.Ici 0) t) →
        Tendsto p atTop (𝓝 0)) := by sorry

end SSLWithoutPairs
