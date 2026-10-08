-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_22
-- name    : RobbinsMonroSA.Conv.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:40.257592+00:00
-- url     : https://prove2.me/theorems/16daa902-c58a-4064-b69a-de78a1a13508
-- title:
--   (21)–(22), p. 403 — Pr[|x_n − θ| ≤ A_n] = 1
-- statement:
--   Under (4) with constant $C>0$, positive step sizes $a_n > 0$, and the process (7)–(8) started at $x_1$, let
--   $$A_n = |x_1 - \theta| + [C + |\alpha|](a_1 + a_2 + \cdots + a_{n-1}). \tag{21}$$
--   Then for every $n$,
--   $$\Pr[\,|x_n - \theta| \le A_n\,] = 1.$$
--
--   The almost-sure bound (22) localises the iterates, so that only the behaviour of $M$ on $|x-\theta| \le A_n$ matters at step $n$.
--
--   **Formalization Note** Indices are 0-based: `bigA x1 θ C α a n` $= |x_1-\theta| + (C+|\alpha|)\sum_{i<n} a_i$ is the paper's $A_{n+1}$, the bound for Lean's `x n` (the paper's $x_{n+1}$). Only the positivity half of (6) is assumed. The conclusion is "almost surely".
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 403, (21)–(22)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (21)–(22), p. 403. From (4) and (7), `Pr[|x_n - θ| ≤ A_n] = 1` for every `n`
(0-based: `bigA x1 θ C α a n` is the paper's `A_{n+1}`). -/
theorem eq_22 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (hpos : ∀ n, 0 < a n) :
    ∀ n, ∀ᵐ ω ∂P, |x n ω - θ| ≤ bigA x1 θ C α a n := by sorry

end RobbinsMonroSA.Conv
