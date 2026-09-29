-- Prove2me | Theorems.Thm_UnderstandingML_mcdiarmid_inequality_pi
-- name    : UnderstandingML.mcdiarmid_inequality_pi
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-26T16:10:02.577906+00:00
-- url     : https://prove2.me/theorems/720e41d3-9f41-4c2a-a23d-6342dfaf6392
-- title:
--   Lemma 26.4 (McDiarmid): w.p. ≥ 1−δ, |f(X) − E f(X)| ≤ c√(ln(2/δ) m/2) for f with bounded differences c
-- statement:
--   **Lemma 26.4 (McDiarmid's inequality).** Let $V$ be a set and let $f:V^m\to\mathbb{R}$ be a function of $m$ variables such that, for some $c$, for all $i\in[m]$ and all $x_1,\dots,x_m,x_i'\in V$,
--
--   $$|f(x_1,\dots,x_m)-f(x_1,\dots,x_{i-1},x_i',x_{i+1},\dots,x_m)|\le c .$$
--
--   Let $X_1,\dots,X_m$ be independent random variables taking values in $V$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--
--   $$\big|f(X_1,\dots,X_m)-\mathbb{E}[f(X_1,\dots,X_m)]\big|\le c\sqrt{\ln(2/\delta)\,m/2}.$$
--
--   This is the concentration inequality used in Chapter 26 to turn the bound on the expected representativeness (Lemma 26.2) into the high-probability generalization bounds of Theorem 26.5: the representativeness and the empirical Rademacher complexity both change by at most $2c/m$ when a single example is replaced.
--
--   **Formalization Note** Independence is modelled by the product measure $\mu_1\otimes\cdots\otimes\mu_m$ of probability measures on a measurable space $V$ (`Measure.pi μ`), and the random vector is the identity on $V^m$. The function $f$ is assumed measurable. The conclusion bounds the probability of the failure event $\{c\sqrt{\ln(2/\delta)m/2}<|f-\mathbb{E}f|\}$ by $\delta$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 26, Lemma 26.4 (McDiarmid's inequality), used in the proof of Theorem 26.5

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 26.4 (McDiarmid's inequality)** (p. 377). Let `V` be a set and `f : V^m → ℝ` a function
of `m` variables such that, for some `c`, changing any single coordinate changes `f` by at most
`c`. Let `X₁, …, X_m` be independent random variables with values in `V` (here: the coordinates
under a product of probability measures `μ₁ ⊗ ⋯ ⊗ μ_m`). Then, with probability at least `1 − δ`,
`|f(X₁, …, X_m) − E f(X₁, …, X_m)| ≤ c √(ln(2/δ) m / 2)`. `f` is measurable. -/
theorem mcdiarmid_inequality_pi {V : Type*} [MeasurableSpace V] (m : ℕ) (μ : Fin m → Measure V)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin m → V) → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : ∀ (x : Fin m → V) (i : Fin m) (v : V), |f x - f (Function.update x i v)| ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi μ {x | c * Real.sqrt (Real.log (2 / δ) * m / 2) <
      |f x - ∫ y, f y ∂(Measure.pi μ)|} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
