-- Prove2me | Theorems.Thm_SAARate_Sharp_theorem_2_1
-- name    : SAARate.Sharp.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:53.471048+00:00
-- url     : https://prove2.me/theorems/a957bb85-d18d-4b63-a75c-ddefa7ae706d
-- title:
--   Theorem 2.1, p. 5 — at a sharp minimum x̄, w.p.1 for N large enough the SAA problem has the unique optimal solution x̂_N = x̄
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$, $\Theta\subseteq\mathbb R^m$ and $h:\mathbb R^m\times\Omega\to\mathbb R$, and consider the true problem and its sample average approximation
--   $$
--   \min_{x\in\Theta}\bigl\{f(x):=\mathbb E_P h(x,\omega)\bigr\}, \qquad \min_{x\in\Theta}\Bigl\{\hat f_N(x):=N^{-1}\sum_{j=1}^N h(x,\omega^j)\Bigr\},
--   $$
--   where $\omega^1,\omega^2,\dots$ is an i.i.d. sample from $P$. Suppose that
--
--   1. for every $\omega\in\Omega$ the function $h(\cdot,\omega)$ is convex;
--   2. the expected value function $f$ is well defined and finite valued;
--   3. the set $\Theta$ is closed and convex;
--   4. Assumption (A) holds: $\bar x\in\Theta$ is the unique optimal solution of the true problem, and for some $c>0$, $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$.
--
--   Then w.p.1 for $N$ large enough the approximating problem has a unique optimal solution $\hat x_N$ and $\hat x_N=\bar x$:
--   $$
--   \operatorname*{argmin}_{x\in\Theta}\hat f_N(x)=\{\bar x\}.
--   $$
--
--   "W.p.1 for $N$ large enough" means: for almost every sample path there is $N^*$, depending on the path, such that the statement holds for every $N\ge N^*$. At a sharp minimum, therefore, the Monte Carlo approximation does not merely converge to the true solution: it returns it exactly once the sample is large enough.
--
--   **Formalization Note.** Assumption 2 is encoded as integrability of $h(x,\cdot)$ for every $x$. The sample is one i.i.d. sequence on an auxiliary probability space $(S,Q)$, and $\hat f_N$ uses its first $N$ terms; the conclusion is "for $Q$-almost every path, eventually in $N$". "Unique optimal solution equal to $\bar x$" is the set equality $\operatorname{argmin}_\Theta\hat f_N=\{\bar x\}$, which includes existence.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 5, Theorem 2.1 (with (1.1), (1.2) p. 1 and Assumption (A) p. 4)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_2_1 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : E m) (hA : AssumptionA P h Θ xbar)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, ∀ᶠ N in atTop, argminOn (saaObj h (fun j => ω j s) N) Θ = {xbar} := by sorry

end SAARate.Sharp
