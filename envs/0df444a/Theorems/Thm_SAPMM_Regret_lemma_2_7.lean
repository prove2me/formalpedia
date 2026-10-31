-- Prove2me | Theorems.Thm_SAPMM_Regret_lemma_2_7
-- name    : SAPMM.Regret.lemma_2_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:27.830672+00:00
-- url     : https://prove2.me/theorems/3185b28b-63eb-4794-a797-70067fe33fdd
-- title:
--   Lemma 2.7 (part 1), p. 11 — drift lemma: E[Z(t)] ≤ θ + t_0δ_max + t_0(4δ_max²/ζ) log(8δ_max²/ζ²)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$ such that $\mathcal F_0=\{\emptyset,\Omega\}$, and let $(Z(t))_{t\ge0}$ be a real process adapted to it with $Z(0)=0$. Suppose there are an integer $t_0\ge1$ and real constants $\theta>0$, $\delta_{\max}>0$ and $0<\zeta\le\delta_{\max}$ such that
--
--   1. $|Z(t+1)-Z(t)|\le\delta_{\max}$ for every $t\ge0$, and
--   2. for every $t\ge1$, almost surely,
--   $$
--   \mathbb E\big[Z(t+t_0)-Z(t)\,\big|\,\mathcal F_t\big]\le\begin{cases}t_0\delta_{\max}&\text{if }Z(t)<\theta,\\-t_0\zeta&\text{if }Z(t)\ge\theta.\end{cases}
--   $$
--
--   Then for every $t\ge1$,
--
--   $$
--   \mathbb E[Z(t)]\le\theta+t_0\delta_{\max}+t_0\frac{4\delta_{\max}^2}{\zeta}\log\frac{8\delta_{\max}^2}{\zeta^2}.
--   $$
--
--   This is the drift lemma of Yu, Neely and Wei, quoted by the paper without proof. Applied to $Z(t)=\|\lambda^t\|$ it bounds the expected multiplier norm uniformly in $t$.
--
--   **Formalization Note** The page imposes both conditions "for all $t\in\{1,2,\dots\}$". Read literally, part 1 is then false: $Z(0)=0$ and $Z(t)=M-(t-1)\delta_{\max}$ for $t\ge1$ satisfies the remaining hypotheses and has $\mathbb E[Z(1)]=M$ arbitrary. The increment bound is therefore imposed for every $t\ge0$, as in Yu–Neely–Wei's use; PMMSopt satisfies it since $\|\lambda^1\|\le\sigma\nu_g$. Part 2 of the lemma (the tail bound) is not stated. `Adapted` means each $Z(t)$ is $\mathcal F_t$-measurable; $\log$ is the natural logarithm, with positive argument since $\zeta\le\delta_{\max}$.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, p. 11, Lemma 2.7, part 1 (from Yu, Neely and Wei [20])

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- Lemma 2.7, part 1, p. 11 (Yu–Neely–Wei): a process with bounded increments and negative
drift above `θ` has bounded expectation. The increment bound is imposed for every `t ≥ 0`. -/
theorem lemma_2_7 {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (hℱ0 : ℱ 0 = ⊥) (Z : ℕ → Ω → ℝ) (hZ : Adapted ℱ Z)
    (hZ0 : ∀ ω, Z 0 ω = 0) (t0 : ℕ) (ht0 : 1 ≤ t0) (θ δmax ζ : ℝ) (hθ : 0 < θ)
    (hδ : 0 < δmax) (hζ : 0 < ζ) (hζδ : ζ ≤ δmax)
    (hinc : ∀ t ω, |Z (t + 1) ω - Z t ω| ≤ δmax)
    (hdrift : ∀ t, 1 ≤ t → ∀ᵐ ω ∂μ,
      μ[fun ω => Z (t + t0) ω - Z t ω | ℱ t] ω ≤
        if Z t ω < θ then (t0 : ℝ) * δmax else -((t0 : ℝ) * ζ)) :
    ∀ t, 1 ≤ t → ∫ ω, Z t ω ∂μ ≤
      θ + t0 * δmax + t0 * (4 * δmax ^ 2 / ζ) * Real.log (8 * δmax ^ 2 / ζ ^ 2) := by sorry

end SAPMM.Regret
