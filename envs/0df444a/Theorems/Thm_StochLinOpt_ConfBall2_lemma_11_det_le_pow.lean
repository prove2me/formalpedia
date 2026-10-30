-- Prove2me | Theorems.Thm_StochLinOpt_ConfBall2_lemma_11_det_le_pow
-- name    : StochLinOpt.ConfBall2.lemma_11_det_le_pow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:54:00.815443+00:00
-- url     : https://prove2.me/theorems/8d952aa8-1a8e-44f5-ac2a-81901f7794ab
-- title:
--   Lemma 11: $\det A_t\le t^n\det A_1$
-- statement:
--   Let $D\subset\mathbb R^n$ span $\mathbb R^n$, let $b$ be a barycentric spanner for $D$, and let $x_1,x_2,\dots$ be any decisions in $D$. Then for every round $t\ge1$,
--
--   $$\det A_t\le t^n\,\det A_1 .$$
--
--   With the spanner normalized to the standard basis, $\det A_1=1$ and this is the paper's $\det A_t\le t^n$. It caps the growth of the log-determinant potential.
--
--   Differences from the source:
--   - generalization: spanner normalized to the standard basis (§5, p. 6), so A_1 = I → any barycentric spanner b of a full-rank D; the bound carries the factor det A_1; reason: with b_i = e_i, det A_1 = 1 and the statement is the paper's
--   - generalization: the algorithm's decisions → any decisions in D; reason: the proof uses only x_τ ∈ D (coordinates in [−1, 1] in the spanner basis)
--   - encoding: for all t → for all t ≥ 1; reason: rounds are 1-based; A_t is defined for t ≥ 1
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Lemma 11, p. 8

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
import Definitions.Def_StochLinOpt_ConfBall2_gram
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Lemma 11** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Lemma 11, p. 8: "For all t, det At ≤ tn").

If every decision lies in `D`, then `det A_t ≤ tⁿ · det A_1` for every round `t ≥ 1`.

**Formalization Note** The paper normalizes the spanner to the standard basis (§5, p. 6), where
`det A_1 = 1`; for a general barycentric spanner the bound carries the factor `det A_1`.
Rounds are 1-based. -/
theorem lemma_11_det_le_pow {n : ℕ} {D : Set (Fin n → ℝ)} (hfull : Submodule.span ℝ D = ⊤)
    {b : Fin n → Fin n → ℝ} (hb : IsBarycentricSpanner D b) {x : ℕ → Fin n → ℝ}
    (hx : ∀ τ, 1 ≤ τ → x τ ∈ D) (t : ℕ) (ht : 1 ≤ t) :
    (gram b x t).det ≤ (t : ℝ) ^ n * (gram b x 1).det := by sorry

end StochLinOpt.ConfBall2
