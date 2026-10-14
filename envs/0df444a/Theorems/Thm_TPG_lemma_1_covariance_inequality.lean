-- Prove2me | Theorems.Thm_TPG_lemma_1_covariance_inequality
-- name    : TPG.lemma_1_covariance_inequality
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:09:22.351444+00:00
-- url     : https://prove2.me/theorems/18295d98-5e09-40b5-9509-ace9b7cea168
-- title:
--   Lemma 1 — covariance inequality for bounded variables under strong mixing (Doukhan)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $\mathcal U,\mathcal V\subseteq\mathcal F$ be sub-$\sigma$-algebras. Their **strong mixing coefficient** is
--
--   $$\alpha(\mathcal U,\mathcal V)=\sup_{A\in\mathcal U,\;B\in\mathcal V}\bigl|\mathbb P(A\cap B)-\mathbb P(A)\,\mathbb P(B)\bigr| .$$
--
--   Let $X$ be a real random variable measurable with respect to $\mathcal U$ and $Y$ one measurable with respect to $\mathcal V$, both bounded, with $\|X\|_\infty=\inf\{M\ge0:\mathbb P(|X|>M)=0\}$.
--
--   **Lemma.**
--
--   $$\bigl|\operatorname{Cov}(X,Y)\bigr|\le 4\,\alpha(\mathcal U,\mathcal V)\,\|X\|_\infty\,\|Y\|_\infty .$$
--
--   This inequality converts a bound on mixing coefficients into a bound on covariances of bounded functionals of separated parts of a process; the source uses it in the consistency proof of the variance estimator.
--
--   **Formalization Note** The formal statement takes real numbers $a$, $b$, $\alpha$ with $|X|\le a$ and $|Y|\le b$ almost surely and $|\mathbb P(A\cap B)-\mathbb P(A)\mathbb P(B)|\le\alpha$ for all $A\in\mathcal U$, $B\in\mathcal V$, and concludes $|\operatorname{Cov}(X,Y)|\le4\alpha ab$. Since such $a,b,\alpha$ are nonnegative and the bound is monotone in each, this is equivalent to the displayed inequality with the essential suprema and the supremum.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Appendix A.4, p. 27, Lemma 1; cited there as Lemma 3 of P. Doukhan, Mixing: Properties and Examples, Lecture Notes in Statistics 85, Springer, 1994, https://doi.org/10.1007/978-1-4612-2642-0.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem lemma_1_covariance_inequality {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (mU mV : MeasurableSpace Ω) (hU : mU ≤ mΩ) (hV : mV ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable[mU] X) (hY : Measurable[mV] Y)
    (a b α : ℝ) (hXa : ∀ᵐ ω ∂μ, |X ω| ≤ a) (hYb : ∀ᵐ ω ∂μ, |Y ω| ≤ b)
    (hα : ∀ A B : Set Ω, MeasurableSet[mU] A → MeasurableSet[mV] B →
      |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ α) :
    |cov[X, Y; μ]| ≤ 4 * α * a * b := by sorry
end TPG
