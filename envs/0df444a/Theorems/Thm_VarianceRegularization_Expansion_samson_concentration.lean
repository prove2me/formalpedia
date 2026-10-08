-- Prove2me | Theorems.Thm_VarianceRegularization_Expansion_samson_concentration
-- name    : VarianceRegularization.Expansion.samson_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:15:23.462894+00:00
-- url     : https://prove2.me/theorems/50a11cf4-e54a-4a8e-a62f-b1a97977238f
-- title:
--   Lemma A.2: Samson convex Lipschitz concentration
-- statement:
--   Let $Z_1,\ldots,Z_n$ be independent, possibly differently distributed random variables supported on $[a,b]$, where $n\ge1$ and $a<b$. Let $f:\mathbb R^n\to\mathbb R$ be convex and $L$-Lipschitz on $[a,b]^n$ in Euclidean distance, with $L>0$. For every $t\ge0$, each of the upper and lower tail probabilities is bounded by
--
--   $$\max\{\Pr(f(Z)\ge\mathbb Ef(Z)+t),\Pr(f(Z)\le\mathbb Ef(Z)-t)\}\le\exp\left(-\frac{t^2}{2L^2(b-a)^2}\right).$$
--
--   This is the appendix's concentration input for functions of a bounded independent sample.
--
--   **Formalization Note** The independent coordinates are represented by a product of arbitrary probability laws. The Lipschitz condition explicitly uses $\sqrt{\sum_i(x_i-y_i)^2}$, since the default norm on `Fin n → ℝ` is not Euclidean.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 33, Lemma A.2; citing Samson [39], Corollary 3

import Mathlib

open MeasureTheory

namespace VarianceRegularization.Expansion

/-- Lemma A.2 (Samson, Corollary 3), p. 33. The coordinate laws may differ. The Lipschitz
condition uses the Euclidean square-sum distance, not the sup norm on `Fin n → ℝ`. -/
theorem samson_concentration {n : ℕ} (hn : 0 < n) (a b L t : ℝ)
    (hab : a < b) (hL : 0 < L) (ht : 0 ≤ t)
    (P : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, P i (Set.Icc a b) = 1)
    (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (Set.pi Set.univ (fun _ : Fin n => Set.Icc a b)) f)
    (hLip : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc a b),
      ∀ y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc a b),
        |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    max ((Measure.pi P) {z | (∫ x, f x ∂(Measure.pi P)) + t ≤ f z})
        ((Measure.pi P) {z | f z ≤ (∫ x, f x ∂(Measure.pi P)) - t}) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2 * (b - a) ^ 2))) := by sorry

end VarianceRegularization.Expansion
