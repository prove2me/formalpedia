-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_9
-- name    : SeqRankAgg.Optimality.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:46.176162+00:00
-- url     : https://prove2.me/theorems/4c2ced01-38cb-406c-a370-5041912d7dbf
-- title:
--   Lemma 9 (corrected), p. 23 — level-crossing bound for a Lipschitz random field
-- statement:
--   Let $W\subset\mathbb R^{m}$ be compact and satisfy the volume condition of Assumption A2 with constant $\delta_b>0$: $\operatorname{vol}(B(\theta,s)\cap W)\ge\min\{\delta_b s^{m},1\}$ for all $\theta\in W$ and $s>0$. Let $\{\zeta(\theta):\theta\in W\}$ be a jointly measurable random field on a probability space $(\Omega,\mathbb P)$ whose sample paths are almost surely $\kappa_L$-Lipschitz on $W$, with $\kappa_L>0$. Let $b\in\mathbb R$ and $\gamma>0$ satisfy $\delta_b(\gamma/\kappa_L)^{m}\le1$. Then
--
--   $$
--   \mathbb P\Big(\sup_{\theta\in W}\zeta(\theta)\ge b\Big)\le\int_W\mathbb P\big(\zeta(\theta)\ge b-\gamma\big)\,d\theta\times\frac{\kappa_L^{m}}{\gamma^{m}\delta_b}.
--   $$
--
--   Here $m=K-1$ is the dimension of the parameter space. The lemma converts pointwise tail bounds of a random field into a bound for its supremum; the paper uses it for the log-likelihood fields indexed by the alternative parameter.
--
--   **Formalization Note** As printed (for every positive $\gamma$) the lemma is false: on $W=[0,1]$ with $\zeta\equiv Z$ a fair coin, $b=1$, $\gamma=1/2$, $\kappa_L=1/10$, $\delta_b=1$, the left side is $1/2$ and the right side $1/10$. The proof's lower bound $\operatorname{vol}(B(\theta^*,\gamma/\kappa_L)\cap W)\ge\gamma^{m}\delta_b/\kappa_L^{m}$ uses the first branch of the minimum in A2, so the statement adds the guard $\delta_b(\gamma/\kappa_L)^{m}\le1$ (it holds for small $\gamma$, the regime in which the paper applies the lemma). The page's $U\subset\mathbb R^K$ and $W$ are the same set here, of dimension $K-1$ as in A2; $\kappa_L>0$ is required (with $\kappa_L=0$ the right side vanishes). Norms and balls are sup-norm on $\mathbb R^{m}$, consistently in A2 and in the Lipschitz condition. The maximum is written as "some $\theta\in W$ has $\zeta(\theta)\ge b$", which equals it for continuous paths on compact $W$.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 23, Lemma 9; proof pp. 39–40, Appendix D (statement corrected, see Formalization Note)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_9 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Wset : Set (Fin m → ℝ)) (hW : IsCompact Wset)
    (δb : ℝ) (hδb : 0 < δb)
    (hA2 : ∀ θ ∈ Wset, ∀ s : ℝ, 0 < s →
      min (δb * s ^ m) 1 ≤ (volume (Metric.ball θ s ∩ Wset)).toReal)
    (ζ : Ω → (Fin m → ℝ) → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (κL : ℝ) (hκL : 0 < κL)
    (hLip : ∀ᵐ ω ∂P, ∀ θ ∈ Wset, ∀ θ' ∈ Wset, |ζ ω θ - ζ ω θ'| ≤ κL * ‖θ - θ'‖)
    (b γ : ℝ) (hγ : 0 < γ) (hguard : δb * (γ / κL) ^ m ≤ 1) :
    P {ω | ∃ θ ∈ Wset, b ≤ ζ ω θ} ≤
      (∫⁻ θ in Wset, P {ω | b - γ ≤ ζ ω θ}) *
        ENNReal.ofReal (κL ^ m / (γ ^ m * δb)) := by sorry

end SeqRankAgg.Optimality
