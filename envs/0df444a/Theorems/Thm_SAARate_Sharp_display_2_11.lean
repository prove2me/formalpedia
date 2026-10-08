-- Prove2me | Theorems.Thm_SAARate_Sharp_display_2_11
-- name    : SAARate.Sharp.display_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:49.92478+00:00
-- url     : https://prove2.me/theorems/80288bcc-fc5e-43b5-b674-a1981869e71b
-- title:
--   (2.11), proof of Theorem 2.1, p. 6 — w.p.1 for N large enough f̂′_N(x̄, d) > 0 on T_Θ(x̄) ∩ S^{m−1}
-- statement:
--   Assume the hypotheses of Theorem 2.1: $h(\cdot,\omega)$ is convex for every $\omega$, $f(x)=\mathbb E_P h(x,\omega)$ is well defined and finite valued, $\Theta\subseteq\mathbb R^m$ is closed and convex, and Assumption (A) holds at $\bar x$. Let $\omega^1,\omega^2,\dots$ be an i.i.d. sample from $P$, $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$, and $S^{m-1}=\{d\in\mathbb R^m:\|d\|=1\}$. Then w.p.1 for $N$ large enough
--   $$
--   \hat f'_N(\bar x,d)>0\qquad\forall\, d\in T_\Theta(\bar x)\cap S^{m-1}. \tag{2.11}
--   $$
--
--   "W.p.1 for $N$ large enough" means: for almost every sample path there is $N^*$, depending on the path, such that the display holds for every $N\ge N^*$. Together with the convexity of the approximating problem this makes $\bar x$ a sharp minimum of (1.2).
--
--   **Formalization Note.** $T_\Theta(\bar x)$ is Mathlib's `posTangentConeAt Θ x̄` (for convex $\Theta$, the closure of $\mathbb R_+(\Theta-\bar x)$). The sample is one i.i.d. sequence on a probability space $(S,Q)$, and $\hat f_N$ uses its first $N$ terms. Assumption (ii) is encoded as integrability of $h(x,\cdot)$ for every $x$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 6, proof of Theorem 2.1, (2.11)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem display_2_11 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : E m) (hA : AssumptionA P h Θ xbar)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, ∀ᶠ N in atTop, ∀ d ∈ posTangentConeAt Θ xbar ∩ Metric.sphere 0 1,
      0 < dirDeriv (saaObj h (fun j => ω j s) N) xbar d := by sorry

end SAARate.Sharp
