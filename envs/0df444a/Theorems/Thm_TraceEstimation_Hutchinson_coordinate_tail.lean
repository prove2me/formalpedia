-- Prove2me | Theorems.Thm_TraceEstimation_Hutchinson_coordinate_tail
-- name    : TraceEstimation.Hutchinson.coordinate_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:28:39.228515+00:00
-- url     : https://prove2.me/theorems/9cb43448-82dc-4e18-873d-b8f67a3407aa
-- title:
--   Proof of Theorem 7.1, p. 8:11 — per-direction tail $\le \delta/\mathrm{rank}(A)$ for $M \ge 6\epsilon^{-2}\ln(2\,\mathrm{rank}(A)/\delta)$
-- statement:
--   Let $\alpha \in \mathbb{R}^n$ be a unit vector, $r \ge 1$ an integer, $0 < \epsilon \le 1/2$ and $0 < \delta < 1$. Let $z_1, \ldots, z_M \in \mathbb{R}^n$ be independent random vectors with independent Rademacher entries and put $y_i = \alpha^T z_i$. If the number of samples satisfies
--
--   $$M \ge 6\epsilon^{-2}\ln\!\left(\frac{2r}{\delta}\right),$$
--
--   then
--
--   $$\Pr\left(\left|\frac{1}{M}\sum_{i=1}^{M} y_i^2 - 1\right| \ge \epsilon\right) \le \frac{\delta}{r}.$$
--
--   In the proof of Theorem 7.1, $\alpha$ is one of the orthonormal eigenvectors of $A$ and $r = \mathrm{rank}(A)$; a union bound over the $\mathrm{rank}(A)$ eigenvectors with nonzero eigenvalue then controls all directions at once.
--
--   **Formalization Note** The page states this step without a range on $\epsilon$; it follows from Lemma 7.2 because $\frac{M}{2}\bigl(\frac{\epsilon^2}{2} - \frac{\epsilon^3}{3}\bigr) \ge \frac{M\epsilon^2}{6}$, which holds exactly when $\epsilon \le 1/2$, so $\epsilon \le 1/2$ is stated (the same correction as in Theorem 7.1). The page's $y_{ij}$, the $j$-th entry of $U^Tz_i$, is written here as $\alpha^Tz_i$ for a unit vector $\alpha$, which avoids the page's inconsistent indexing of $U$. The integer $r$ replaces $\mathrm{rank}(A)$ so that the statement does not depend on a matrix. $M$ is a natural number; the hypothesis forces $M \ge 1$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:11, Section 7, proof of Theorem 7.1, second display

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- Proof of Theorem 7.1 (Avron–Toledo, p. 8:11, second display), in the corrected form the
proof establishes. Let `α ∈ ℝⁿ` be a unit vector (`αᵀα = 1`; in the proof, a row of the
eigenvector matrix), `r ≥ 1` an integer (in the proof, `rank(A)`), `0 < ε ≤ 1/2`,
`0 < δ < 1`, and let `z_1, …, z_M ∈ ℝⁿ` be independent with i.i.d. Rademacher entries,
`y_i = αᵀ z_i`. If `M ≥ 6 ε⁻² ln(2r/δ)` then
`Pr(|(1/M) ∑_{i=1}^M y_i² - 1| ≥ ε) ≤ δ / r`.
The page states no range for `ε`; the step from Lemma 7.2 needs
`(M/2)(ε²/2 - ε³/3) ≥ M ε²/6`, which holds exactly when `ε ≤ 1/2`. -/
theorem coordinate_tail {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) (r : ℕ) (hr : 1 ≤ r)
    (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1) (M : ℕ)
    (hMbound : 6 * ε⁻¹ ^ 2 * Real.log (2 * (r : ℝ) / δ) ≤ (M : ℝ)) :
    (hutchinsonSampleMeasure n M).real
        {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤ δ / r := by sorry

end TraceEstimation.Hutchinson
