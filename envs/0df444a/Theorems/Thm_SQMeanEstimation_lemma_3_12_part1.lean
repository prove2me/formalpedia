-- Prove2me | Theorems.Thm_SQMeanEstimation_lemma_3_12_part1
-- name    : SQMeanEstimation.lemma_3_12_part1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:41.711307+00:00
-- url     : https://prove2.me/theorems/f5b860cf-7846-4dcf-a562-3624a57c294d
-- title:
--   Lemma 3.12 (1) — $\|x\|_r\le\|x\|_\infty^{1-p/r}\|x\|_p^{p/r}$
-- statement:
--   For every $x\in\mathbb R^d$ and all real exponents $0<p<r$,
--   $$
--   \|x\|_r\le\|x\|_\infty^{1-p/r}\cdot\|x\|_p^{p/r},
--   $$
--   where $\|x\|_s=(\sum_i|x_i|^s)^{1/s}$ and $\|x\|_\infty=\max_i|x_i|$.
--
--   The inequality interpolates between a small and a large exponent; in the proof of Theorem 3.15 it bounds the $\ell_q$ size of a vector whose coordinates are uniformly small (eq. (3)).
--
--   Differences from the source:
--   - encoding: x ∈ ℝᵈ, ‖x‖ₚ = (Σ|xᵢ|ᵖ)^{1/p} → x : Fin d → ℝ, lqNorm p x = (∑ i, |x i| ^ p) ^ (1/p) with Real.rpow; reason: Lean convention; same values (paper coordinate i is index i − 1)
--   - encoding: ‖x‖_∞ → Mathlib's sup norm ‖x‖ on Fin d → ℝ (0 when d = 0); reason: Lean convention; equals maxᵢ |xᵢ|
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Lemma 3.12(1), p.16

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm

namespace SQMeanEstimation

/-- **Lemma 3.12, part 1.**
Feldman, Guzmán, Vempala, *Statistical Query Algorithms for Mean Vector Estimation and Stochastic
Convex Optimization*, arXiv:1512.09170v2, Lemma 3.12(1), p.16: "For any x ∈ ℝᵈ and any two
0 < p < r: ‖x‖_r ≤ ‖x‖_∞^{1−p/r} · ‖x‖_p^{p/r}".

**Formalization Note.** `‖x‖_∞` is Mathlib's sup norm `‖x‖` on `Fin d → ℝ` (`= maxᵢ |xᵢ|`, and
`0` for `d = 0`). `‖x‖_p`, `‖x‖_r` are `lqNorm`. Powers are `Real.rpow`. -/
theorem lemma_3_12_part1 {d : ℕ} (p r : ℝ) (hp : 0 < p) (hpr : p < r) (x : Fin d → ℝ) :
    lqNorm r x ≤ ‖x‖ ^ (1 - p / r) * lqNorm p x ^ (p / r) := by sorry

end SQMeanEstimation
