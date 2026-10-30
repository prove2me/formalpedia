-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_9_sum_min_width_sq
-- name    : StochLinOpt.ConfBall2.lemma_9_sum_min_width_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:54:37.285045+00:00
-- url     : https://prove2.me/theorems/051c5aef-95fb-4f9c-8381-1698fef248ad
-- title:
--   Lemma 9 (corrected: $t\ge3$): $\sum_{\tau=1}^t\min(w_\tau^2,1)\le 2n\ln t$
-- statement:
--   Let $D\subset\mathbb R^n$ span $\mathbb R^n$, let $b$ be a barycentric spanner for $D$, and let $x_1,x_2,\dots$ be any decisions in $D$. Then for every $t\ge3$,
--
--   $$\sum_{\tau=1}^t\min\bigl(w_\tau^2,1\bigr)\le 2n\ln t .$$
--
--   This is the elliptical-potential bound of the paper: the squared widths of the chosen decisions cannot stay large for long.
--
--   Differences from the source:
--   - correction: for all t → for all t ≥ 3; reason: false at t = 1 (right side 0, left side w_1² > 0) and at t = 2: n = 1, D = [−1, 1], b_1 = 1, x_1 = x_2 = 1 give 1 + 1/2 = 1.5 > 2 ln 2 ≈ 1.386; the printed constant is kept
--   - generalization: the algorithm's decisions → any decisions in D; reason: the proof uses only Lemmas 10 and 11, which hold for any decisions in D
--   - generalization: spanner normalized to the standard basis e_1, …, e_n (§5, p. 6, 'without loss of generality') → any barycentric spanner b of a full-rank D, with A_1 = Σ_i b_i b_iᵀ; reason: the paper's normalization is the instance b_i = e_i, where A_1 = I
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 9, p. 8

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_width
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 9 (corrected: t ≥ 3)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 9, p. 8: "We have for all t
Σ_{τ=1}^t min (w2τ, 1) ≤ 2n ln t").

If every decision lies in `D`, then for every `t ≥ 3`,
`Σ_{τ=1}^t min(w_τ², 1) ≤ 2n ln t`.

**Formalization Note** The printed "for all t" is false at `t = 1` (the right side is `0`) and at
`t = 2` (`n = 1`, `D = [−1, 1]`, `b_1 = 1`, `|x_1| = |x_2| = 1` give `1.5 > 2 ln 2`); the
statement is restricted to `t ≥ 3`, with the printed constant. The decisions are any sequence in
`D`. -/
theorem lemma_9_sum_min_width_sq {n : ℕ} {D : Set (Fin n → ℝ)} (hfull : Submodule.span ℝ D = ⊤)
    {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b) {x : ℕ → Fin n → ℝ}
    (hx : ∀ τ, 1 ≤ τ → x τ ∈ D) (t : ℕ) (ht : 3 ≤ t) :
    ∑ τ ∈ Finset.Icc 1 t, min (width b x τ ^ 2) 1 ≤ 2 * n * Real.log t := by sorry

end StochLinOpt.ConfBall2
