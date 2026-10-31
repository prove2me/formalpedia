-- Prove2me | Theorems.Thm_SQMeanEstimation_lemma_3_12_part2
-- name    : SQMeanEstimation.lemma_3_12_part2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:43.952624+00:00
-- url     : https://prove2.me/theorems/99c2417c-56d3-4750-b25f-39018a1eabfc
-- title:
--   Lemma 3.12 (2) — $\|x\|_p\le a^{1-r/p}\|x\|_r^{r/p}$ (corrected: $|x_i|$ in the minimum)
-- statement:
--   Let $0<p<r$ and $x\in\mathbb R^d$, and let $a>0$ satisfy $a\le|x_i|$ for every $i$ with $x_i\ne0$ (for $x\ne0$, e.g. $a=\min\{|x_i|:x_i\neq0\}$). Then
--   $$
--   \|x\|_p\le a^{1-r/p}\cdot\|x\|_r^{r/p}.
--   $$
--
--   This reverse interpolation bounds a low-exponent norm of a vector whose nonzero coordinates are bounded away from $0$; the proof of Theorem 3.15 uses it for eq. (4).
--
--   Differences from the source:
--   - correction: a = min{xᵢ | xᵢ ≠ 0} → a bounds |xᵢ| from below on the nonzero coordinates; reason: the printed statement is false for vectors with a negative coordinate: d = 1, x = (−1/2), p = 1, r = 2 gives a = −1/2 and right side a^{−1}·(1/4) = −1/2 < 1/2 = ‖x‖₁; the proof needs 0 < a ≤ |xᵢ|, and every use in the paper is on nonnegative vectors
--   - generalization: a the minimum of the nonzero |xᵢ| → every a > 0 with a ≤ |xᵢ| whenever xᵢ ≠ 0; reason: the minimum is one such a whenever x ≠ 0 (for x = 0 the minimum is undefined), so the statement specializes to the corrected source
--   - encoding: x ∈ ℝᵈ, ‖x‖ₚ = (Σ|xᵢ|ᵖ)^{1/p} → x : Fin d → ℝ, lqNorm p x = (∑ i, |x i| ^ p) ^ (1/p) with Real.rpow; reason: Lean convention; same values (paper coordinate i is index i − 1)
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Lemma 3.12(2), p.16

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm

namespace SQMeanEstimation

/-- **Lemma 3.12, part 2 (corrected: |xᵢ| in the minimum).**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Lemma 3.12(2), p.16: "For any x ∈ ℝᵈ and any two
0 < p < r: … Let a = min_{i∈[d]}{xᵢ | xᵢ ≠ 0}. Then ‖x‖_p ≤ a^{1−r/p} · ‖x‖_r^{r/p}."

Stated for every `a > 0` that bounds `|xᵢ|` from below on the nonzero coordinates; the minimum
`min{|xᵢ| : xᵢ ≠ 0}` is one such `a` whenever `x ≠ 0`.

**Formalization Note.** The printed minimum is over the signed `xᵢ`; with a negative coordinate it
is false (`d = 1`, `x = (−1/2)`, `p = 1`, `r = 2`: the right side is `−1/2 < 1/2`), and the
proof uses `0 < a ≤ |xᵢ|`. Powers are `Real.rpow`. -/
theorem lemma_3_12_part2 {d : ℕ} (p r : ℝ) (hp : 0 < p) (hpr : p < r) (x : Fin d → ℝ)
    (a : ℝ) (ha : 0 < a) (hax : ∀ i, x i ≠ 0 → a ≤ |x i|) :
    lqNorm p x ≤ a ^ (1 - r / p) * lqNorm r x ^ (r / p) := by sorry

end SQMeanEstimation
