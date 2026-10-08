-- Prove2me | Theorems.Thm_SAARate_SharpLD_theorem_3_1
-- name    : SAARate.SharpLD.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:50.514211+00:00
-- url     : https://prove2.me/theorems/f588d5a1-47db-4265-9699-b76b630ddf56
-- title:
--   Theorem 3.1, p. 11 — under (A) and (B), ∃ β > 0 with limsup_N N⁻¹ log P(ℰ^c_N) ≤ −β
-- statement:
--   Let $P$ be a probability measure on a measurable space $(\Omega,\mathcal F)$, let $h:\mathbb R^m\times\Omega\to\mathbb R$, and let $\Theta\subseteq\mathbb R^m$. Write $f(x)=\mathbb E_P\,h(x,\omega)$ for the true objective (1.1) and $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$ for the sample average objective (1.2) built from an i.i.d. sample $\omega^1,\omega^2,\dots$ with law $P$. The assumptions of Theorem 2.1 are: (i) $h(\cdot,\omega)$ is convex for every $\omega$; (ii) $f$ is well defined and finite valued; (iii) $\Theta$ is closed and convex; (iv) Assumption (A): $f$ has the unique minimizer $\bar x$ on $\Theta$ and there is $c>0$ with $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$. Assumption (B) asks for a $\kappa>0$ with $\sup_{d\in S^{m-1}}|h'_\omega(\bar x,d)|\le\kappa$ for $P$-almost every $\omega$, where $h'_\omega(\bar x,d)$ is the directional derivative of $h(\cdot,\omega)$ at $\bar x$ in direction $d$ and $S^{m-1}$ is the unit sphere.
--
--   Let $A_N$ be the set of optimal solutions of the SAA problem $\min_{x\in\Theta}\hat f_N(x)$ and let $\mathcal E_N$ be the event that $A_N$ is nonempty and $A_N=\{\bar x\}$ (3.7), i.e. that the SAA problem has the unique optimal solution $\hat x_N=\bar x$.
--
--   **Theorem 3.1.** Suppose that the assumptions (i)–(iv) of Theorem 2.1 are satisfied and that Assumption (B) holds. Then there is a constant $\beta>0$ such that
--   $$\limsup_{N\to\infty}\frac1N\log P(\mathcal E_N^c)\le-\beta .$$
--
--   So at a sharp minimum the probability that the sample average approximation fails to return exactly the true solution decays exponentially in the sample size.
--
--   **Formalization Note** The sample $\omega^1,\omega^2,\dots$ is one i.i.d. sequence of $\Omega$-valued maps on a separate probability space $(S,Q)$, each with law $P$; $\hat f_N$ uses its first $N$ terms. The rate is stated in the equivalent $\varepsilon$-form: there is $\beta>0$ such that for every $\varepsilon>0$, eventually in $N$, $Q(\mathcal E_N^c)\le e^{-(\beta-\varepsilon)N}$; this avoids the logarithm of a probability that may be $0$. $\mathcal E_N^c$ is not shown to be measurable, so $Q$ is its outer measure, which makes the upper bound stronger. "f finite valued" is the hypothesis that each $h(x,\cdot)$ is $P$-integrable. The directional derivatives in (B) are true limits because $h(\cdot,\omega)$ is convex.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 11, Theorem 3.1, (3.7), (3.8); hypotheses of Theorem 2.1, p. 5; Assumption (A), p. 4; Assumption (B), p. 9

import Mathlib
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAARate.SharpLD

theorem theorem_3_1 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : SAARate.Sharp.E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : SAARate.Sharp.E m) (hA : SAARate.Sharp.AssumptionA P h Θ xbar)
    (κ : ℝ) (hB : AssumptionB P h xbar κ)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∃ β > 0, ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ ≠ {xbar}} ≤
        ENNReal.ofReal (Real.exp (-(β - ε) * N)) := by sorry

end SAARate.SharpLD
