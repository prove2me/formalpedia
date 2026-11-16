-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_lemma_4_1
-- name    : QMatVecLB.ConvexOpt.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:23.06596+00:00
-- url     : https://prove2.me/theorems/d0d0ac95-a8c3-41d5-aea2-1479b4d2c74d
-- title:
--   Lemma 4.1 — trace correlation as an n-fold convolution
-- statement:
--   Let $n\ge1$ and let $b_{\mathrm d},b_{\mathrm{od}}:\mathbb R\to\mathbb R$ be pointwise nonnegative Schwartz functions with $\|b_{\mathrm d}\|_1=\|b_{\mathrm{od}}\|_1=1$. Let
--   $$b(A)=\prod_{i=1}^n b_{\mathrm d}(A_{ii})\prod_{i\ne j}b_{\mathrm{od}}(A_{ij})$$
--   (Eq. (25)) and $\beta=\det(-\frac1{2\pi i}\partial_X)b$ (Eq. (23)). Then for every bounded measurable $d:\mathbb R\to\mathbb R$ and $D(A)=d(\operatorname{tr}A)$,
--   $$\int_{\mathbb R^{n\times n}}D(A)\,d\beta(A)=\Big(-\frac1{2\pi i}\Big)^n\int_{\mathbb R}d(\tau)\,(b_{\mathrm d}')^{*n}(\tau)\,d\tau,$$
--   where $b_{\mathrm d}'$ is the derivative and $f^{*n}$ is the $n$-fold convolution of $f$ with itself.
--
--   The correlation of a trace-dependent decision function with the witness thus depends only on the diagonal factor; Lemma 4.2 evaluates it for a threshold function.
--
--   Differences from the source:
--   - encoding: n-fold convolution, Eq. (32): f^{∗n}(τ) = ∫_{ℝ^{n−1}} f(a₁)…f(a_{n−1}) f(τ−a₁−…−a_{n−1}) da → convPow (b_d′) (n−1): b_d′ convolved with itself n times by iterated Mathlib convolution; reason: the two agree by Fubini for integrable f, and b_d′ is Schwartz
--   - encoding: n × n matrices with n a positive integer → hypothesis 1 ≤ n; reason: Eq. (32) is undefined for n = 0; excludes only the degenerate case
--   - encoding: pointwise nonnegative Schwartz functions b_d, b_od : ℝ → ℝ → elements of Mathlib SchwartzMap ℝ ℝ with nonnegativity hypotheses; reason: the same class
--   - encoding: ∥f∥₁ → ∫ |f| (Lebesgue); reason: definition of the L¹ norm
--   - encoding: ∫ D(A) dβ(A) with dβ = β(X) dX → Bochner integral of d(tr A)·β(A) against matrixLebesgue; reason: the definition of the complex measure dβ on p. 7
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 4.1, PDF p. 9 (printed p. 8).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem lemma_4_1 (n : ℕ) (hn : 1 ≤ n) (bd bod : SchwartzMap ℝ ℝ)
    (hbd_nonneg : ∀ x, 0 ≤ bd x) (hbod_nonneg : ∀ x, 0 ≤ bod x)
    (hbd_norm : (∫ x, |bd x|) = 1) (hbod_norm : (∫ x, |bod x|) = 1)
    (d : ℝ → ℝ) (hd_meas : Measurable d) (hd_bdd : ∃ C : ℝ, ∀ x, |d x| ≤ C) :
    (∫ A : RMat n, (d A.trace : ℂ) * detWitness (productB (fun x => bd x) (fun x => bod x)) A
        ∂matrixLebesgue n) =
      witnessCoeff ^ n *
        ∫ τ : ℝ, (d τ : ℂ) * (convPow (deriv (fun x => bd x)) (n - 1) τ : ℂ) := by sorry

end QMatVecLB.ConvexOpt.Supplement
