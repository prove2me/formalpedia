-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_lemma_4_3
-- name    : QMatVecLB.ConvexOpt.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:23.703675+00:00
-- url     : https://prove2.me/theorems/7e3fc230-fa4f-4929-95b9-f39bc2cb3177
-- title:
--   Lemma 4.3 — support and mass of the identity term
-- statement:
--   Assume the set-up of Section 4 as in Lemma 4.2 ($n$ positive and even, $\theta=(n-1)/2$, $b_{\mathrm d}=\mathbf 1_{[0,1]}*g_\delta$ with $\delta\le\frac1{6n}$, $w=16n^{3/2}$, $b_{\mathrm{od}}=\frac1w\mathbf 1_{[0,w]}*g_{w/2}$, for arbitrary smooth even nonnegative unit-mass mollifiers $g_\delta$, $g_{w/2}$ supported on $[-\delta,\delta]$, $[-w/2,w/2]$). Let
--   $$\beta_{\mathrm{id}}(A)=\Big(-\frac1{2\pi i}\Big)^n\prod_{i=1}^nb_{\mathrm d}'(A_{ii})\prod_{i\ne j}b_{\mathrm{od}}(A_{ij}),\qquad\beta_{\overline{\mathrm{id}}}=\beta-\beta_{\mathrm{id}},$$
--   and $\mathcal P=\{A:|\theta-\operatorname{tr}A|\ge\frac13,\ \|A\|_{\max}\le24n^{3/2}\}$. Then:
--
--   1. $\operatorname{supp}\beta_{\mathrm{id}}\subseteq\mathcal P$;
--   2. $\|\beta_{\mathrm{id}}\|_1=1/\pi^n$;
--   3. if $\|b_{\mathrm{od}}'\|_1\le\frac18n^{-3/2}$, then
--   $$\|\beta_{\overline{\mathrm{id}}}\|_1\le\tfrac18n^{-1/2}\,\|\beta_{\mathrm{id}}\|_1 .$$
--
--   These give the promise containment and the two masses $\|\xi_0\|_1$, $\|\xi_1\|_1$ (with $\xi_0=\beta_{\mathrm{id}}$, $\xi_1=\beta_{\overline{\mathrm{id}}}$) in the proof of Theorem 4.4.
--
--   Differences from the source:
--   - encoding: standing set-up of §4 (n even, θ = (n−1)/2, D = 1_{tr A ≥ θ}, smooth even nonnegative mollifiers g_δ (δ ≤ 1/(6n)) and g_{w/2} with unit L¹ norm, b_d = 1_{[0,1]} ∗ g_δ, w = 16n^{3/2}, b_od = (1/w)1_{[0,w]} ∗ g_{w/2}) → hypotheses 0 < n, Even n, δ ≤ 1/(6n), IsMollifier g_δ δ, IsMollifier g_w (w/2), with b_d = bDiag g_δ and b_od = bOff n g_w, universally quantified over the mollifiers; reason: the lemma holds for every admissible choice; 0 < n only excludes the degenerate n = 0, where no mollifier with δ ≤ 1/(6n) exists in any case
--   - encoding: smooth; supported on [−δ, δ] → ContDiff ℝ ∞; Function.support g ⊆ [−δ, δ]; reason: C^∞; since [−δ, δ] is closed, this equals closed support in [−δ, δ]
--   - encoding: supp β_id → tsupport (closure of the set where β_id ≠ 0); reason: the support of a continuous function is its closed support; this is the strongest reading, and the one the proof establishes
--   - encoding: ∥β_id∥₁ and ∥β_{\overline{id}}∥₁ → ∫ ‖·‖ against matrixLebesgue, together with an explicit Integrable conclusion; reason: the Bochner integral returns 0 on non-integrable functions; asserting integrability matches the page's finite norms
--   - encoding: ∥A∥_max → published maxNorm (entrywise sup norm); reason: identical
--   - encoding: the proviso ∥b_od′∥₁ ≤ (1/8) n^{−3/2} → kept as an implication hypothesis, with ∥b_od′∥₁ = ∫ |deriv b_od|; reason: as on the page; the §4 choice gives equality, so the hypothesis is satisfiable
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 4.3, PDF p. 10 (printed p. 9).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem lemma_4_3 (n : ℕ) (hn : 0 < n) (heven : Even n)
    (δ : ℝ) (hδ : δ ≤ 1 / (6 * (n : ℝ))) (gδ : ℝ → ℝ) (hgδ : IsMollifier gδ δ)
    (gw : ℝ → ℝ) (hgw : IsMollifier gw (offWidth n / 2)) :
    tsupport (betaId (n := n) (bDiag gδ) (bOff n gw)) ⊆ tracePromise n ∧
    (Integrable (betaId (n := n) (bDiag gδ) (bOff n gw)) (matrixLebesgue n) ∧
      (∫ A : RMat n, ‖betaId (bDiag gδ) (bOff n gw) A‖ ∂matrixLebesgue n) = 1 / Real.pi ^ n) ∧
    ((∫ x : ℝ, |deriv (bOff n gw) x|) ≤ (1 / 8) * (n : ℝ) ^ (-(3 : ℝ) / 2) →
      Integrable (betaBar (n := n) (bDiag gδ) (bOff n gw)) (matrixLebesgue n) ∧
      (∫ A : RMat n, ‖betaBar (bDiag gδ) (bOff n gw) A‖ ∂matrixLebesgue n) ≤
        (1 / 8) * (n : ℝ) ^ (-(1 : ℝ) / 2) *
          ∫ A : RMat n, ‖betaId (bDiag gδ) (bOff n gw) A‖ ∂matrixLebesgue n) := by sorry

end QMatVecLB.ConvexOpt.Supplement
