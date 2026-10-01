-- Prove2me | Theorems.Thm_TraceEstimation_UnitVector_mixed_rD_bound
-- name    : TraceEstimation.UnitVector.mixed_rD_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:43:13.955127+00:00
-- url     : https://prove2.me/theorems/bfd58d30-4bc1-4441-b30d-d072a40a4d20
-- title:
--   Theorem 8.4, proof — $r_D(\mathcal FA\mathcal F^T) \le 2n\eta\ln(4n^2/\delta)$ w.p. $1-\delta/2$
-- statement:
--   Let $n \ge 1$, let $F$ be an orthogonal $n\times n$ seed matrix with $\eta = \max_{i,j}|F_{ij}|^2$, let $\mathcal F = FD$ be the random mixing matrix, let $A \in \mathbb{R}^{n\times n}$ be symmetric positive semi-definite, and let $0 < \delta < 1$. Then with probability at least $1-\delta/2$ over $D$, for all $j$,
--
--   $$0 \le (\mathcal F A\mathcal F^T)_{jj} \le 2\eta\ln\left(\frac{4n^2}{\delta}\right)\mathrm{trace}(A),$$
--
--   and consequently
--
--   $$r_D(\mathcal FA\mathcal F^T) \le 2n\eta\ln\left(\frac{4n^2}{\delta}\right).$$
--
--   This is the step of the proof of Theorem 8.4 that turns the entrywise bound of Lemma 8.3 into a bound on the diagonal of the mixed matrix, so that Theorem 8.2 applies to $\mathcal FA\mathcal F^T$ with a controlled $r_D$.
--
--   **Formalization Note** The event is the conjunction of the diagonal bounds and the $r_D$ bound, over the diagonal $d$ of $D$ under `signMeasure n`. No hypothesis $\mathrm{trace}(A) > 0$ is added: for $A = 0$ both parts hold (Lean's $r_D(0) = 0$ and the right-hand sides are non-negative for $\delta < 1$).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:13, Section 8, proof of Theorem 8.4, second and third displays

import Mathlib
import Definitions.Def_TraceEstimation_UnitVector_mixingMatrix
import Definitions.Def_TraceEstimation_UnitVector_rD

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix Real

/-- Avron–Toledo, proof of Theorem 8.4 (p. 8:13), the bound on the diagonal of the mixed matrix:
let `F` be an orthogonal `n × n` seed matrix (`n ≥ 1`) with `η = max |F_ij|²`, `𝓕 = F D` the random
mixing matrix, `A` a symmetric positive semi-definite `n × n` matrix, and `0 < δ < 1`. With
probability at least `1 - δ/2` over `D`, for all `j`,
`0 ≤ (𝓕 A 𝓕ᵀ)_jj ≤ 2η ln(4n²/δ) trace(A)`, and consequently
`r_D(𝓕 A 𝓕ᵀ) ≤ 2nη ln(4n²/δ)`. -/
theorem mixed_rD_bound {n : ℕ} (hn : 0 < n)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ * F = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 ≤ (signMeasure n).real
      {d | (∀ j, 0 ≤ (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) j j ∧
              (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) j j ≤
                2 * eta F * Real.log (4 * (n : ℝ) ^ 2 / δ) * A.trace) ∧
        rD (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) ≤
          2 * (n : ℝ) * eta F * Real.log (4 * (n : ℝ) ^ 2 / δ)} := by sorry

end TraceEstimation.UnitVector
