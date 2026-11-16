-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_lemma_4_2
-- name    : QMatVecLB.ConvexOpt.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:53.667827+00:00
-- url     : https://prove2.me/theorems/18a79741-2531-489a-ba76-026e2b7bc842
-- title:
--   Lemma 4.2 — exact correlation with the trace threshold
-- statement:
--   Assume the set-up of Section 4: $n$ is a positive even integer, $\theta=(n-1)/2$ and $D(A)=\mathbf 1_{\operatorname{tr}A\ge\theta}$. Let $g_\delta$ be a smooth, even, nonnegative mollifier with $\|g_\delta\|_1=1$ supported on $[-\delta,\delta]$, where $\delta\le\frac1{6n}$, and put $b_{\mathrm d}=\mathbf 1_{[0,1]}*g_\delta$. Let $w=16n^{3/2}$, let $g_{w/2}$ be a smooth, even, nonnegative mollifier with $\|g_{w/2}\|_1=1$ supported on $[-w/2,w/2]$, and put $b_{\mathrm{od}}=\frac1w\mathbf 1_{[0,w]}*g_{w/2}$. Let $\beta$ be defined by Eqs. (23) and (25). Then
--   $$\Big|\int_{\mathbb R^{n\times n}}D(A)\,d\beta(A)\Big|=\binom{n-1}{\frac n2-1}\Big/(2\pi)^n .$$
--
--   This is the numerator of the failure bound (11) in the proof of the trace lower bound, Theorem 4.4.
--
--   Differences from the source:
--   - encoding: standing set-up of §4 (n even, θ = (n−1)/2, D = 1_{tr A ≥ θ}, smooth even nonnegative mollifiers g_δ (δ ≤ 1/(6n)) and g_{w/2} with unit L¹ norm, b_d = 1_{[0,1]} ∗ g_δ, w = 16n^{3/2}, b_od = (1/w)1_{[0,w]} ∗ g_{w/2}) → hypotheses 0 < n, Even n, δ ≤ 1/(6n), IsMollifier g_δ δ, IsMollifier g_w (w/2), with b_d = bDiag g_δ and b_od = bOff n g_w, universally quantified over the mollifiers; reason: the lemma holds for every admissible choice; 0 < n only excludes the degenerate n = 0, where no mollifier with δ ≤ 1/(6n) exists in any case
--   - encoding: smooth; supported on [−δ, δ] → ContDiff ℝ ∞; Function.support g ⊆ [−δ, δ]; reason: C^∞; since [−δ, δ] is closed, this equals closed support in [−δ, δ]
--   - encoding: binomial coefficient C(n−1, n/2−1) → Nat.choose (n−1) (n/2−1) with natural-number subtraction and division; reason: n is even and positive, so n−1, n/2 and n/2−1 are exact
--   - encoding: |∫ D dβ| → complex norm of the Bochner integral of D(A)·β(A) against matrixLebesgue; reason: the definition of dβ on p. 7
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 4.2, PDF p. 10 (printed p. 9).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem lemma_4_2 (n : ℕ) (hn : 0 < n) (heven : Even n)
    (δ : ℝ) (hδ : δ ≤ 1 / (6 * (n : ℝ))) (gδ : ℝ → ℝ) (hgδ : IsMollifier gδ δ)
    (gw : ℝ → ℝ) (hgw : IsMollifier gw (offWidth n / 2)) :
    ‖∫ A : RMat n, (traceDecision (traceTheta n) A : ℂ) *
        detWitness (productB (bDiag gδ) (bOff n gw)) A ∂matrixLebesgue n‖ =
      ((Nat.choose (n - 1) (n / 2 - 1) : ℕ) : ℝ) / (2 * Real.pi) ^ n := by sorry

end QMatVecLB.ConvexOpt.Supplement
