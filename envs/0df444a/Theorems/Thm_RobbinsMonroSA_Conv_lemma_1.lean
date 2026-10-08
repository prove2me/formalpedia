-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_lemma_1
-- name    : RobbinsMonroSA.Conv.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:49.918123+00:00
-- url     : https://prove2.me/theorems/fc46a0c8-294e-4a55-a6dc-4cb5ebdec9d0
-- title:
--   Lemma 1, p. 403 — if d_n ≥ k_n b_n with k_n ≥ 0 and Σ a_n k_n = ∞, then b = 0
-- statement:
--   Assume the standing assumptions of §3: (4) with constant $C>0$, (5), (6) and the process (7)–(8). Suppose there is a sequence $\{k_n\}$ of nonnegative constants such that
--   $$d_n \ge k_n b_n \ \text{ for all } n, \qquad \sum_{n=1}^{\infty} a_n k_n = \infty. \tag{19}$$
--   Then $b = \lim_{n\to\infty} b_n = 0$.
--
--   Lemma 1 is the abstract criterion from which both convergence theorems follow.
--
--   **Formalization Note** Indices are 0-based. "$\sum a_n k_n = \infty$" is the divergence of the partial sums to $+\infty$; the conclusion is $b_n \to 0$. The standing assumptions (4), (5), (6) of §3, which the lemma's sentence does not repeat, are hypotheses.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 403, Lemma 1, with (19) on p. 402

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- Lemma 1, p. 403, with (19), p. 402. Under the standing assumptions (4)–(8) of §3, if
nonnegative constants `k_n` satisfy `d_n ≥ k_n b_n` and `Σ a_n k_n = ∞`, then `b_n → 0`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) (h6 : StepCond6 a)
    (k : ℕ → ℝ) (hk : ∀ n, 0 ≤ k n)
    (h19a : ∀ n, k n * msd P x θ n ≤ dSeq P H α θ x n)
    (h19b : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * k n) atTop atTop) :
    Tendsto (fun n => msd P x θ n) atTop (𝓝 0) := by sorry

end RobbinsMonroSA.Conv
