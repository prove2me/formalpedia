-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_lemma_2
-- name    : RobbinsMonroSA.Conv.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:13:18.405629+00:00
-- url     : https://prove2.me/theorems/e85fba6e-833b-4f57-838e-ac8faa6f5b62
-- title:
--   Lemma 2, p. 403 — if k̄_n ≥ K/A_n (K > 0, n large) and (26) hold, then b = 0
-- statement:
--   Assume the standing assumptions of §3: (4) with constant $C>0$, (5), (6) and the process (7)–(8). Suppose that for some constant $K > 0$ and all sufficiently large $n$,
--   $$\bar k_n \ge \frac{K}{A_n}, \tag{25}$$
--   where $\bar k_n$ is the infimum (23) of $(M(x)-\alpha)/(x-\theta)$ over $0 < |x-\theta| \le A_n$ and $A_n$ is given by (21), and that
--   $$\sum_{n=2}^{\infty} \frac{a_n}{a_1 + \cdots + a_{n-1}} = \infty. \tag{26}$$
--   Then $b = \lim_{n\to\infty} b_n = 0$.
--
--   Lemma 2 converts a growth condition on $M$ near $\theta$ into mean-square convergence; Theorems 1 and 2 verify (25).
--
--   **Formalization Note** Indices are 0-based (`bigA … n` is the paper's $A_{n+1}$). (25) is stated without forming the infimum: for some $K>0$ and some $N$, for all $n \ge N$, $K/A_n \le (M(z)-\alpha)/(z-\theta)$ whenever $0<|z-\theta|\le A_n$; this is exactly $\bar k_n \ge K/A_n$, including the empty-range case. (26) is divergence of partial sums. The standing assumptions (4), (5), (6) are hypotheses.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 403, Lemma 2, (25)–(26)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- Lemma 2, p. 403. Under the standing assumptions (4)–(8) of §3, if (25)
`k̄_n ≥ K / A_n` holds for some `K > 0` and all sufficiently large `n` (stated as: `K / A_n` is a
lower bound of `(M(z) - α)/(z - θ)` on `0 < |z - θ| ≤ A_n`), and (26) holds, then `b_n → 0`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) (h6 : StepCond6 a)
    (h25 : ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z : ℝ, 0 < |z - θ| →
      |z - θ| ≤ bigA x1 θ C α a n →
        K / bigA x1 θ C α a n ≤ (regressionFn H z - α) / (z - θ))
    (h26 : StepCond26 a) :
    Tendsto (fun n => msd P x θ n) atTop (𝓝 0) := by sorry

end RobbinsMonroSA.Conv
