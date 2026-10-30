-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_theorem_4_freedman
-- name    : StochLinOpt.ConfBall2.theorem_4_freedman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:57:17.980876+00:00
-- url     : https://prove2.me/theorems/8bcbafed-98d8-4a93-b9fc-dbd8267c14b5
-- title:
--   Theorem 4 (Freedman): $P(\sum X_i\ge a,\ V\le v)\le\exp\bigl(-a^2/(2v+2ab/3)\bigr)$
-- statement:
--   Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_i)_{i\ge0}$, and let $X_1,\dots,X_T$ be a martingale difference sequence: each $X_i$ is $\mathcal F_i$-measurable and integrable with $\mathbb E(X_i\mid\mathcal F_{i-1})=0$. Suppose $X_i\le b$ almost surely for every $i$, and let
--
--   $$V=\sum_{i=1}^T\mathbb E\bigl(X_i^2\mid\mathcal F_{i-1}\bigr)$$
--
--   be the sum of conditional variances (with values in $[0,\infty]$). Then for every $a>0$ and $v>0$,
--
--   $$P\Bigl(\sum_{i=1}^T X_i\ge a\ \text{ and }\ V\le v\Bigr)\le\exp\Bigl(\frac{-a^2}{2v+2ab/3}\Bigr).$$
--
--   This Bernstein-type inequality lets the step bound be large as long as the accumulated conditional variance is small; it is applied in Lemma 14 with $b=\sqrt{\beta_t}$.
--
--   **Formalization Note** The conditional second moment is Mathlib's conditional expectation of the nonnegative function $X_i^2$, valued in $[0,\infty]$, so no square-integrability is assumed.
--
--   Differences from the source:
--   - reading: V = Σ_{i=1}^n Var(X_i | X_1, …, X_{i−1}) → V = Σ_{i=1}^T; reason: n is not bound in the theorem; the sequence is X_1, …, X_T
--   - generalization: conditioning on X_1, …, X_{i−1} (the natural filtration) → any filtration F, with X_i F_i-measurable and conditioning on F_{i−1}; reason: the natural filtration F_i = σ(X_1, …, X_i) is an instance
--   - encoding: Var(X_i | X_1, …, X_{i−1}) → E(X_i² | F_{i−1}) in [0, ∞] (conditional Lebesgue expectation), no square-integrability assumed; reason: for a martingale difference the conditional variance is the conditional second moment; V ≤ v fails where V = ∞
--   - generalization: b a uniform upper bound on the steps X_i → X_i ≤ b almost surely; reason: a pointwise bound is an instance
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Theorem 4, p. 6 (quoting Freedman 1975)

import Mathlib
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Theorem 4 (Freedman)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Theorem 4, p. 6: "Suppose X1, . . . , XT is a martingale
difference sequence, and b is an uniform upper bound on the steps Xi. Let V denote the sum of
conditional variances, V = Σ_{i=1}^n Var (Xi | X1, . . . , Xi−1). Then, for every a, v > 0,
Prob(Σ Xi ≥ a and V ≤ v) ≤ exp(−a²/(2v + 2ab/3))").

Let `F` be a filtration and `X_1, …, X_T` a martingale difference sequence with respect to it
(`X_i` is `F_i`-measurable and integrable, `E(X_i | F_{i−1}) = 0`) with `X_i ≤ b` almost surely.
Let `V = Σ_{i=1}^T E(X_i² | F_{i−1})`. Then for all `a, v > 0`,
`P(Σ_{i=1}^T X_i ≥ a and V ≤ v) ≤ exp(−a²/(2v + 2ab/3))`.

**Formalization Note** The printed upper summation index `n` is read as `T`. The filtration is
arbitrary (the paper's is the natural one, `F_i = σ(X_1, …, X_i)`). The conditional variance of a
martingale difference is its conditional second moment, which is taken as Mathlib's conditional
Lebesgue expectation `P⁻[· | ·]` of `X_i²` with values in `[0, ∞]`, so no square-integrability is
assumed; `V ≤ v` fails where `V = ∞`. -/
theorem theorem_4_freedman {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℕ m) (X : ℕ → Ω → ℝ) (T : ℕ) {a b v : ℝ}
    (ha : 0 < a) (hv : 0 < v)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, StronglyMeasurable[F i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | F (i - 1)] =ᵐ[P] 0)
    (hstep : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b) :
    P {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P⁻[fun ω' => ENNReal.ofReal (X i ω' ^ 2) | F (i - 1)] ω
          ≤ ENNReal.ofReal v}
      ≤ ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * v + 2 * a * b / 3))) := by sorry

end StochLinOpt.ConfBall2
