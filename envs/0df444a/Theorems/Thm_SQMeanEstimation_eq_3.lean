-- Prove2me | Theorems.Thm_SQMeanEstimation_eq_3
-- name    : SQMeanEstimation.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:46.567955+00:00
-- url     : https://prove2.me/theorems/6741eef3-4a82-4b7e-b4b9-829fc2f95736
-- title:
--   Eq. (3) — $\|u^<\|_q^q\le(4/n)^{q-1}\|u^<\|_1\le n^{1-q}2^{(j+3)q-3}$ (corrected: final "=" is "≤")
-- statement:
--   Let $q\in(1,2)$, $n>0$, $j\in\mathbb N$, and let $u\in\mathbb R^d$ have $u_i\ge0$ for all $i$ and $\|u\|_1\le2^{(j+1)q-1}$ (eq. (2)). With $u^<_i=u_i\mathbf 1_{\{u_i<4/n\}}$,
--   $$
--   \|u^<\|_q^q\le\Big(\frac4n\Big)^{q-1}\|u^<\|_1\le n^{1-q}\cdot2^{(j+3)q-3}.
--   $$
--
--   This bounds the error contributed by the coordinates that the zeroing step may remove.
--
--   Differences from the source:
--   - correction: (4/n)^{q−1}·‖u^<‖₁ = n^{1−q}·2^{(j+3)q−3} → (4/n)^{q−1}·‖u^<‖₁ ≤ n^{1−q}·2^{(j+3)q−3}; reason: the equality is false: for u = 0 the left side is 0 and the right side is positive; the derivation from eq. (2) gives ≤, which is all the proof uses
--   - generalization: u = 2ʲ·w̄^{+,j} → any u with uᵢ ≥ 0 and ∑ uᵢ ≤ 2^{(j+1)q−1}; reason: the paper's u is nonnegative and satisfies eq. (2), so the statement specializes to the source
--   - encoding: ‖·‖_q^q and ‖·‖₁ → ∑ i, |x i| ^ q and ∑ i, |x i|; reason: the definitions of these quantities
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, eq. (3), p.18

import Mathlib
import Definitions.Def_SQMeanEstimation_lowPart

namespace SQMeanEstimation

/-- **Eq. (3) — bound on the small coordinates (corrected: final "=" is "≤").**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, eq. (3), p.18: "Now by Lemma 3.12 and eq.(2), we
have ‖u^<‖_q^q ≤ (4/n)^{q−1} · ‖u^<‖₁ = n^{1−q} · 2^{(j+3)q−3}."

For `q ∈ (1, 2)`, `n > 0`, `j ∈ ℕ` and any `u` with `uᵢ ≥ 0` and `Σ uᵢ ≤ 2^{(j+1)q−1}` (eq. (2)),
with `u^<_i = uᵢ·1_{uᵢ<4/n}`:
`Σ|u^<_i|^q ≤ (4/n)^{q−1}·Σ|u^<_i|` and `(4/n)^{q−1}·Σ|u^<_i| ≤ n^{1−q}·2^{(j+3)q−3}`.

**Formalization Note.** `‖·‖_q^q` is `Σ |·|^q`, `‖·‖₁` is `Σ |·|`, `u^<` is `lowPart n u`. The
printed final "=" is false (for `u = 0` the middle term is `0` and the right side is positive);
the derivation from eq. (2) gives "≤". -/
theorem eq_3 {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    ∑ i, |lowPart n u i| ^ q ≤ (4 / n) ^ (q - 1) * ∑ i, |lowPart n u i| ∧
      (4 / n) ^ (q - 1) * ∑ i, |lowPart n u i| ≤
        n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) := by sorry

end SQMeanEstimation
