-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_sample_std_upper_tail
-- name    : VarianceRegularization.Covering.sample_std_upper_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:09.769624+00:00
-- url     : https://prove2.me/theorems/3aa00fea-3fd0-4dcc-9d25-51d2b3c1222b
-- title:
--   Lemma A.1, first bound — upper tail of the sample standard deviation
-- statement:
--   Let $Z_1, \dots, Z_n$ ($n \ge 1$) be i.i.d. real random variables with values in $[M_0, M_1]$, where $M = M_1 - M_0 > 0$, and let
--   $$
--   s_n^2 = \frac1n \sum_{i=1}^n Z_i^2 - \Big(\frac1n \sum_{i=1}^n Z_i\Big)^2 , \qquad s_n = \sqrt{s_n^2}.
--   $$
--   Then for all $t \ge 0$,
--   $$
--   \mathbb P\left( s_n \ge \sqrt{\mathbb E s_n^2} + t \right) \le \exp\left( - \frac{n t^2}{2 M^2} \right).
--   $$
--
--   The sample standard deviation thus concentrates above its root-mean-square at the sub-Gaussian rate $M/\sqrt n$. In the proof of Theorem 3 it gives $\sqrt{\mathrm{Var}_{\widehat P_n}(f)} \le \sqrt{1 - n^{-1}}\sqrt{\mathrm{Var}(f)} + \sqrt{2tM^2/n}$ with probability at least $1 - e^{-t}$ for a fixed $f$.
--
--   **Formalization Note** The $Z_i$ are the coordinates of $\mathbb R^n$ under the product measure $P^{\otimes n}$, with $P$ a probability measure on $\mathbb R$ giving full mass to $[M_0, M_1]$; $\mathbb E s_n^2$ is the integral of $s_n^2$ under $P^{\otimes n}$. Only the first of the two bounds of Lemma A.1 is stated. The second (lower-tail) bound is derived in the paper from Lemma A.4, which is false as printed, so it is left out. The hypothesis $M > 0$ is needed because $M^2$ is a denominator.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 32, Lemma A.1 (first bound)

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup

open MeasureTheory

namespace VarianceRegularization.Covering

/-- Lemma A.1, first bound (upper tail) (Duchi–Namkoong, arXiv:1610.02581v3, p. 32): let
`Z₁,…,Zₙ` be i.i.d. with law `P` supported in `[M₀, M₁]`, `M = M₁ - M₀ > 0`, and
`s_n² = (1/n) ∑ Zᵢ² - ((1/n) ∑ Zᵢ)²`. For all `t ≥ 0`,
`ℙ(s_n ≥ √(E s_n²) + t) ≤ exp(-n t² / (2M²))`.
The i.i.d. sample is the coordinate process of the product measure `Pⁿ` on `ℝⁿ`.
Only the first of the lemma's two bounds is stated: the second (lower tail) rests on the
paper's Lemma A.4, which is false as printed. `M₀ < M₁` because `M²` is a denominator. -/
theorem sample_std_upper_tail (P : Measure ℝ) [IsProbabilityMeasure P] (M0 M1 : ℝ)
    (hM : M0 < M1) (hP : ∀ᵐ z ∂P, z ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : 0 ≤ t) :
    Measure.pi (fun _ : Fin n => P)
        {Z | Real.sqrt (∫ W, sampleVar W ∂(Measure.pi (fun _ : Fin n => P))) + t
          ≤ Real.sqrt (sampleVar Z)}
      ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * t ^ 2 / (2 * (M1 - M0) ^ 2)))) := by sorry

end VarianceRegularization.Covering
