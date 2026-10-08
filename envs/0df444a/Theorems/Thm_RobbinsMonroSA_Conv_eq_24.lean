-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_24
-- name    : RobbinsMonroSA.Conv.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:51.605362+00:00
-- url     : https://prove2.me/theorems/c117555b-c13b-42d2-b95e-a1b3aa140a86
-- title:
--   (23)–(24), p. 403 — d_n ≥ k̄_n b_n, k̄_n = inf (M(x) − α)/(x − θ) over 0 < |x − θ| ≤ A_n
-- statement:
--   Under (4) with constant $C > 0$, (5), positive step sizes $a_n > 0$, and the process (7)–(8), let
--   $$\bar k_n = \inf\Big[\frac{M(x) - \alpha}{x - \theta}\Big] \quad\text{for } 0 < |x - \theta| \le A_n. \tag{23}$$
--   Then for every $n$,
--   $$d_n \ge \bar k_n\, b_n. \tag{24}$$
--
--   Hence the particular sequence $\{\bar k_n\}$ satisfies the first part of (19) in Lemma 1.
--
--   **Formalization Note** Indices are 0-based (`bigA … n` is the paper's $A_{n+1}$). The infimum is not formed in Lean: the statement says that every lower bound $k$ of $(M(z)-\alpha)/(z-\theta)$ on $0<|z-\theta|\le A_n$ satisfies $d_n \ge k\, b_n$. Since $\bar k_n$ is the greatest such lower bound, this is equivalent to (24) (with $b_n \ge 0$), and it also covers the case of an empty range ($A_n = 0$, where the infimum is $+\infty$ and Lean's real infimum would be $0$).
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 403, (23)–(24)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (23)–(24), p. 403, in lower-bound form. If `k` bounds `(M(z) - α)/(z - θ)` from below on
`0 < |z - θ| ≤ A_n` (so `k ≤ k̄_n`, the infimum of (23)), then `d_n ≥ k b_n`. -/
theorem eq_24 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) (hpos : ∀ n, 0 < a n) :
    ∀ n, ∀ k : ℝ,
      (∀ z : ℝ, 0 < |z - θ| → |z - θ| ≤ bigA x1 θ C α a n →
        k ≤ (regressionFn H z - α) / (z - θ)) →
      k * msd P x θ n ≤ dSeq P H α θ x n := by sorry

end RobbinsMonroSA.Conv
