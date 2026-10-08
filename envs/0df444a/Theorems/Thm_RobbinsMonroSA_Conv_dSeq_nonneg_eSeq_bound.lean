-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_dSeq_nonneg_eSeq_bound
-- name    : RobbinsMonroSA.Conv.dSeq_nonneg_eSeq_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:11:03.148825+00:00
-- url     : https://prove2.me/theorems/e5e39385-090f-4321-97d5-4a124be6efca
-- title:
--   p. 402, after (14) — from (5) d_n ≥ 0, and from (4) 0 ≤ e_n ≤ [C + |α|]²
-- statement:
--   Under the boundedness condition (4) with constant $C>0$, condition (5) on the regression function $M$, and the process (7)–(8), for every $n$,
--   $$d_n \ge 0, \qquad 0 \le e_n \le [C + |\alpha|]^2,$$
--   where $d_n = E[(x_n-\theta)(M(x_n)-\alpha)]$ and $e_n = E[\int (y-\alpha)^2\,dH(y\mid x_n)]$.
--
--   These sign and size facts turn the identity (14) into a supermartingale-type recursion for $b_n$.
--
--   **Formalization Note** Indices are 0-based. All standing assumptions of §3 used by the claim, (4), (5) and (7)–(8), are hypotheses; (6) is not needed.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), p. 402, after (14)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- p. 402, after (14). From (5), `d_n ≥ 0`; from (4), `0 ≤ e_n ≤ [C + |α|]²`. -/
theorem dSeq_nonneg_eSeq_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) :
    ∀ n, 0 ≤ dSeq P H α θ x n ∧ 0 ≤ eSeq P H α x n ∧ eSeq P H α x n ≤ (C + |α|) ^ 2 := by sorry

end RobbinsMonroSA.Conv
