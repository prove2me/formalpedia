-- Prove2me | Theorems.Thm_TraceEstimation_UnitVector_mixing_matrix_entry_bound
-- name    : TraceEstimation.UnitVector.mixing_matrix_entry_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:41:27.70493+00:00
-- url     : https://prove2.me/theorems/71f2224a-7ae8-44ae-bc9d-211aa4c34344
-- title:
--   Lemma 8.3 — entries of $\mathcal F U$ are at most $\sqrt{2\eta\ln(2mn/\delta)}$ w.p. $1-\delta$
-- statement:
--   Let $n \ge 1$, let $F \in \mathbb{R}^{n\times n}$ be an orthogonal seed matrix with $\eta = \max_{i,j}|F_{ij}|^2$, and let $\mathcal F = FD$ be the random mixing matrix, $D$ diagonal with i.i.d. Rademacher entries. Let $U$ be an $n\times m$ matrix with orthonormal columns ($U^TU = I_m$). Then for every $\delta > 0$, with probability at least $1-\delta$, for all $i$ and $j$,
--
--   $$|(\mathcal F U)_{ij}| \le \sqrt{2\eta\ln\left(\frac{2mn}{\delta}\right)} .$$
--
--   The mixing matrix thus prevents the entries of an orthonormal matrix from being large: every entry of $\mathcal FU$ is, with high probability, within a logarithmic factor of $\sqrt{\eta}$. The paper imports this lemma from Ailon and Chazelle (2006) and Avron, Maymounkov and Toledo (2010) without proof.
--
--   **Formalization Note** The probability is over the diagonal $d$ of $D$ under `signMeasure n`; $\mathcal F = $ `mixingMatrix F d`. The paper writes $\eta = \max|F_{ij}|^2$ for the seed $F$; since $|\mathcal F_{ij}| = |F_{ij}|$ almost surely the two readings agree. For $m = 0$ the claim is vacuous in $i, j$; when $2mn/\delta < 1$ Lean's `Real.sqrt` of the negative logarithm is $0$, but then $\delta > 2$ and $1 - \delta < 0$, so the claim is trivially true there as on the page.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:13, Lemma 8.3 (after Ailon and Chazelle 2006; Avron, Maymounkov and Toledo 2010)

import Mathlib
import Definitions.Def_TraceEstimation_UnitVector_mixingMatrix

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix Real

/-- Lemma 8.3 (Avron–Toledo, p. 8:13; Ailon–Chazelle 2006, Avron et al. 2010): let `F` be an
orthogonal `n × n` seed matrix (`n ≥ 1`), `𝓕 = F D` the random mixing matrix with `D` a diagonal
matrix of i.i.d. Rademacher signs, and `U` an `n × m` matrix with orthonormal columns. For every
`δ > 0`, with probability at least `1 - δ`, for all `i` and `j`,
`|(𝓕 U)_ij| ≤ √(2 η ln(2mn/δ))`, where `η = max |F_ij|²`. -/
theorem mixing_matrix_entry_bound {n m : ℕ} (hn : 0 < n)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ * F = 1)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ (signMeasure n).real
      {d | ∀ i j, |(mixingMatrix F d * U) i j| ≤
        Real.sqrt (2 * eta F * Real.log (2 * (m : ℝ) * (n : ℝ) / δ))} := by sorry

end TraceEstimation.UnitVector
