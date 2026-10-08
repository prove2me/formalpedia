-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_27
-- name    : RobbinsMonroSA.Conv.eq_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:13:05.898461+00:00
-- url     : https://prove2.me/theorems/e81f48ca-a0c1-4f0e-962b-c299bc3b5aee
-- title:
--   (26)–(27), p. 403 — for positive a_n, (26) implies Σ a_n = ∞
-- statement:
--   Let $\{a_n\}$ be positive constants satisfying
--   $$\sum_{n=2}^{\infty} \frac{a_n}{a_1 + \cdots + a_{n-1}} = \infty. \tag{26}$$
--   Then
--   $$\sum_{n=1}^{\infty} a_n = \infty. \tag{27}$$
--
--   This is used to show that $A_n \to \infty$, so that the linear growth (28) of $A_n$ in the partial sums of $a_n$ holds for large $n$.
--
--   **Formalization Note** Indices are 0-based. Both "$=\infty$" are divergence of the partial sums to $+\infty$.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 403, (26)–(27)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (26)–(27), p. 403. For positive `a_n`, (26) implies `Σ a_n = ∞`. -/
theorem eq_27 (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (h26 : StepCond26 a) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop := by sorry

end RobbinsMonroSA.Conv
