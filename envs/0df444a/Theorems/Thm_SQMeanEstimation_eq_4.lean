-- Prove2me | Theorems.Thm_SQMeanEstimation_eq_4
-- name    : SQMeanEstimation.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:06.985494+00:00
-- url     : https://prove2.me/theorems/468898d1-f5b8-4dbc-bf95-783e788ce87d
-- title:
--   Eq. (4) — $\|u^>\|_{q/2}^{q/2}\le(1/n)^{q/2-1}\|u^>\|_1\le n^{1-q/2}2^{(j+1)q-1}$
-- statement:
--   Let $q\in(1,2)$, $n>0$, $j\in\mathbb N$, and let $u\in\mathbb R^d$ have $u_i\ge0$ for all $i$ and $\|u\|_1\le2^{(j+1)q-1}$ (eq. (2)). With $u^>_i=u_i\mathbf 1_{\{u_i\ge1/n\}}$,
--   $$
--   \|u^>\|_{q/2}^{q/2}\le\Big(\frac1n\Big)^{q/2-1}\|u^>\|_1\le n^{1-q/2}\cdot2^{(j+1)q-1}.
--   $$
--
--   This bounds the error contributed by the coordinates that the zeroing step keeps.
--
--   Differences from the source:
--   - generalization: u = 2ʲ·w̄^{+,j} → any u with uᵢ ≥ 0 and ∑ uᵢ ≤ 2^{(j+1)q−1}; reason: the paper's u is nonnegative and satisfies eq. (2), so the statement specializes to the source
--   - encoding: ‖·‖_{q/2}^{q/2} and ‖·‖₁ → ∑ i, |x i| ^ (q/2) and ∑ i, |x i|; reason: q/2 < 1, so ‖·‖_{q/2} is not a norm; the power of the expression is the sum itself
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, eq. (4), p.18

import Mathlib
import Definitions.Def_SQMeanEstimation_highPart

namespace SQMeanEstimation

/-- **Eq. (4) — bound on the large coordinates.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, eq. (4), p.18: "Also by Lemma 3.12 and eq.(2), we
have ‖u^>‖_{q/2}^{q/2} ≤ (1/n)^{q/2−1} · ‖u^>‖₁ ≤ n^{1−q/2} · 2^{(j+1)q−1}."

For `q ∈ (1, 2)`, `n > 0`, `j ∈ ℕ` and any `u` with `uᵢ ≥ 0` and `Σ uᵢ ≤ 2^{(j+1)q−1}` (eq. (2)),
with `u^>_i = uᵢ·1_{uᵢ≥1/n}`:
`Σ|u^>_i|^{q/2} ≤ (1/n)^{q/2−1}·Σ|u^>_i|` and `(1/n)^{q/2−1}·Σ|u^>_i| ≤ n^{1−q/2}·2^{(j+1)q−1}`.

**Formalization Note.** `‖·‖_{q/2}^{q/2}` is `Σ |·|^{q/2}` (not a norm, `q/2 < 1`), `‖·‖₁` is
`Σ |·|`, `u^>` is `highPart n u`. Powers are `Real.rpow`. -/
theorem eq_4 {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    ∑ i, |highPart n u i| ^ (q / 2) ≤ (1 / n) ^ (q / 2 - 1) * ∑ i, |highPart n u i| ∧
      (1 / n) ^ (q / 2 - 1) * ∑ i, |highPart n u i| ≤
        n ^ (1 - q / 2) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) := by sorry

end SQMeanEstimation
