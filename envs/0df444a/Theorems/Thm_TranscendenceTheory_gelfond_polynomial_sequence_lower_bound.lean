-- Prove2me | Theorems.Thm_TranscendenceTheory_gelfond_polynomial_sequence_lower_bound
-- name    : TranscendenceTheory.gelfond_polynomial_sequence_lower_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:25:04.957502+00:00
-- url     : https://prove2.me/theorems/4ea65533-b6f5-47e9-9bff-e4bac5c34a16
-- title:
--   Gel'fond criterion: infinitely many lower bounds for polynomial values
-- statement:
--   Let $\theta$ be a transcendental complex number and $c>1$. Let $d_n,t_n$ be strictly increasing positive real sequences tending to infinity, with
--
--   $$
--   d_{n+1}\le c d_n,\qquad t_{n+1}\le c t_n.
--   $$
--
--   For integer polynomials $P_n$ assume $P_n(\theta)\ne0$, $\deg P_n\le d_n$, and every coefficient of $P_n$ has absolute value at most $e^{t_n}$. Then infinitely many indices satisfy
--
--   $$
--   \log|P_n(\theta)|>-(2c+1)d_n(t_n+d_n).
--   $$
--
--   This polynomial form of Gel'fond's criterion rules out uniformly excessive smallness while degrees and logarithmic coefficient bounds grow at controlled rates.
-- source:
--   Senthil Kumar K (2026), Section 3, Lemma 3 and its proof (polynomial formulation), https://doi.org/10.1017/S001309152610145X; the proof cites Brownawell, Lemma 4, and Waldschmidt, Theorem 8.2.1. Indices are shifted to start at zero; unbounded increasing sequences are expressed by StrictMono and Tendsto atTop atTop. No elliptic-function hypothesis is needed.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Order.Filter.AtTopBot.Field

open Filter
open scoped Topology Polynomial

namespace TranscendenceTheory

/-- Polynomial form of Senthil Kumar (2026), Lemma 3 (Gel'fond's criterion). -/
theorem gelfond_polynomial_sequence_lower_bound
    (θ : ℂ) (hθ : Transcendental ℚ θ) (c : ℝ) (hc : 1 < c)
    (d t : ℕ → ℝ)
    (hd_pos : ∀ n, 0 < d n) (ht_pos : ∀ n, 0 < t n)
    (hd_strict : StrictMono d) (ht_strict : StrictMono t)
    (hd_unbounded : Tendsto d atTop atTop) (ht_unbounded : Tendsto t atTop atTop)
    (hd_growth : ∀ n, d (n + 1) ≤ c * d n)
    (ht_growth : ∀ n, t (n + 1) ≤ c * t n)
    (P : ℕ → ℤ[X])
    (h_nonzero : ∀ n, Polynomial.aeval θ (P n) ≠ 0)
    (h_degree : ∀ n, ((P n).natDegree : ℝ) ≤ d n)
    (h_coeff : ∀ n k, |((P n).coeff k : ℝ)| ≤ Real.exp (t n)) :
    ∃ᶠ n in atTop,
      -(2 * c + 1) * d n * (t n + d n) <
        Real.log ‖Polynomial.aeval θ (P n)‖ := by sorry

end TranscendenceTheory
