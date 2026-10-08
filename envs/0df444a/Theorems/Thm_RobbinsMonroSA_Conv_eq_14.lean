-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_14
-- name    : RobbinsMonroSA.Conv.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:36:36.185115+00:00
-- url     : https://prove2.me/theorems/8346b0b4-235e-4095-b6ca-3ff649157ab4
-- title:
--   (14), p. 402, from (11) on p. 401 — b_{n+1} − b_n = a_n² e_n − 2a_n d_n
-- statement:
--   Let $H$ be a Markov kernel of response distributions satisfying the boundedness condition (4) with constant $C > 0$, let $\alpha, \theta \in \mathbb R$, let $\{a_n\}$ be real constants, and let $\{x_n\}, \{y_n\}$ be the Robbins–Monro process (7)–(8) started at the constant $x_1$. With $b_n = E(x_n - \theta)^2$, $d_n = E[(x_n-\theta)(M(x_n)-\alpha)]$ and $e_n = E[\int (y-\alpha)^2\,dH(y\mid x_n)]$, for every $n$,
--   $$b_{n+1} - b_n = a_n^2 e_n - 2 a_n d_n.$$
--
--   This one-step identity, obtained by conditioning on $x_n$ as in (11), is the starting point of all of the paper's convergence arguments.
--
--   **Formalization Note** Indices are 0-based (Lean's `n` is the paper's $n+1$). Only (4) and (7)–(8) are assumed: the identity needs neither (5) nor (6). Condition (4) makes every expectation genuine (the iterates are almost surely bounded).
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), pp. 401–402, (11)–(14)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (11)–(14), pp. 401–402. Under (4) and the process (7)–(8),
`b_{n+1} - b_n = a_n² e_n - 2 a_n d_n` for every `n` (0-based indices). -/
theorem eq_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y) :
    ∀ n, msd P x θ (n + 1) - msd P x θ n =
      a n ^ 2 * eSeq P H α x n - 2 * a n * dSeq P H α θ x n := by sorry

end RobbinsMonroSA.Conv
