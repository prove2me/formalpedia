-- Prove2me | Theorems.Thm_SAARate_Polyhedral_theorem_3_2
-- name    : SAARate.Polyhedral.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:24.082993+00:00
-- url     : https://prove2.me/theorems/812223bd-c719-47b7-9deb-cf2d2e559143
-- title:
--   Theorem 3.2, p. 12, (3.17) — ∃ β > 0, limsup_N N⁻¹ log P(ℳ_N^c) ≤ −β
-- statement:
--   Assume the conditions of Theorem 2.3:
--
--   1. the scenario set $\Omega$ is finite;
--   2. every $h(\cdot,\omega)$ is piecewise linear and convex on $\mathbb R^m$;
--   3. $\Theta$ is closed, convex and polyhedral;
--   4. the optimal set $A$ of the true problem $\min_{x\in\Theta}\mathbb E_Ph(x,\omega)$ is nonempty and bounded.
--
--   Let $\omega^1,\omega^2,\dots$ be an i.i.d. sample from $P$ on a probability space $(S,Q)$, let $A_N$ be the optimal set of the SAA problem $\min_{x\in\Theta}N^{-1}\sum_{j=1}^Nh(x,\omega^j)$, and let
--   $$
--   \mathcal M_N:=\{\,A_N\text{ is nonempty and forms a face of }A\,\}.\tag{3.16}
--   $$
--   Then there is a constant $\beta>0$ such that
--   $$
--   \limsup_{N\to\infty}\frac1N\log Q(\mathcal M_N^c)\le-\beta.\tag{3.17}
--   $$
--
--   The probability that the SAA problem fails to return a face of the true optimal set decays exponentially in the sample size. This is the quantitative form of Theorem 2.3, and it explains why small samples already solve finite piecewise linear stochastic programs exactly.
--
--   **Formalization Note** (3.17) is stated in the equivalent form: for every $\delta>0$, eventually $Q(\mathcal M_N^c)\le e^{-(\beta-\delta)N}$. This avoids the logarithm of a probability that may be $0$. $\mathcal M_N^c$ is not shown to be measurable, so $Q(\mathcal M_N^c)$ is its outer measure; an upper bound on it is the stronger statement. The complement is of the whole event: $A_N$ empty, or $A_N$ not a face of $A$. The empty set is a face of every set, so nonemptiness is stated explicitly.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 12, Theorem 3.2, (3.16), (3.17)

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory Filter

namespace SAARate.Polyhedral

/-- Theorem 3.2, p. 12, (3.17): under the assumptions (i)–(iv) of Theorem 2.3 there is `β > 0`
with `limsup_N N⁻¹ log P(ℳ_N^c) ≤ −β`, where `ℳ_N` (3.16) is the event that the SAA optimal set
`A_N` is nonempty and a face of the true optimal set `A`. Stated in ε-form: for every `δ > 0`,
eventually `P(ℳ_N^c) ≤ exp(−(β − δ) N)`, with `P(ℳ_N^c)` the outer measure. -/
theorem theorem_3_2 {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (hΘp : IsPolyhedral Θ)
    (hA : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ))} ≤
        ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ))) := by sorry

end SAARate.Polyhedral
