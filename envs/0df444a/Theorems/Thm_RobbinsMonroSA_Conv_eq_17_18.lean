-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_17_18
-- name    : RobbinsMonroSA.Conv.eq_17_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:28.090386+00:00
-- url     : https://prove2.me/theorems/f797fc3d-fc59-47ce-ba81-c39bf9973369
-- title:
--   (15)–(18), p. 402 — Σ a_n d_n converges and b = lim b_n has the identity in (18)
-- statement:
--   Under the standing assumptions of §3 — (4) with constant $C>0$, (5), (6) and the process (7)–(8) — the positive-term series $\sum a_n^2 e_n$ and $\sum a_n d_n$ converge, and the limit
--   $$b = \lim_{n\to\infty} b_n = b_1 + \sum_{n=1}^{\infty} a_n^2 e_n - 2\sum_{n=1}^{\infty} a_n d_n$$
--   exists and satisfies $b \ge 0$.
--
--   This reduces mean-square convergence to showing that the limit $b$ is $0$.
--
--   **Formalization Note** Indices are 0-based. Convergence of $\sum a_n d_n$ is `Summable`; the limit $b \ge 0$ is identified with the two series in (18).
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 402, (15)–(18)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (15)–(18), p. 402. Under (4), (5), (6) and the process (7)–(8), the series
`Σ a_n d_n` converges and `lim b_n = b₁ + Σ a_n² e_n - 2 Σ a_n d_n` exists, with `b ≥ 0`. -/
theorem eq_17_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) (h6 : StepCond6 a) :
    Summable (fun n => a n ^ 2 * eSeq P H α x n) ∧
    Summable (fun n => a n * dSeq P H α θ x n) ∧
      ∃ b : ℝ, 0 ≤ b ∧ Tendsto (fun n => msd P x θ n) atTop (𝓝 b) ∧
        b = msd P x θ 0 + (∑' n, a n ^ 2 * eSeq P H α x n) -
          2 * (∑' n, a n * dSeq P H α θ x n) := by sorry

end RobbinsMonroSA.Conv
