-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_eq_hS_ge_hZ
-- name    : SampleCRS.AlmostGreedy.eq_hS_ge_hZ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:37.670095+00:00
-- url     : https://prove2.me/theorems/fe714e11-cfc6-49cb-a101-47c95e293fbc
-- title:
--   §4.1, p.17: comparison with the Poisson expectation
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ satisfy $\sum_jp_j=k$, and let $S$ be the sum of independent Bernoulli variables with biases $p_j$. For $Z\sim\mathrm{Poi}(k)$,
--   $$\mathbb E[h_k(S)]\ge\mathbb E[h_k(Z)].$$
--
--   This is the final comparison after taking the binomial-to-Poisson limit. The separately referenced bounded-function limit is already an Open platform statement and is not posed again here.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: expectations of S and B_N, sums of independent Bernoulli trials → the published pbE counting formula, with constant bias k/N for B_N; reason: the count laws coincide, and total mass k with probabilities at most one implies N ≥ n ≥ k ≥ 1
--   - encoding: expectation under Z ∼ Poi(k) → the published poisE series against poissonMeasure at the nonnegative real k; reason: h takes values in [0,1], so the series converges absolutely and its default value is irrelevant
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, final expectation comparison, p.17

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

open scoped NNReal

namespace SampleCRS.AlmostGreedy

/-- The final expectation inequality obtained on p.17. -/
theorem eq_hS_ge_hZ (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ)) :
    StaticProphetSec.poisE (h k) (k : ℝ≥0) ≤ StaticProphetSec.pbE (h k) p := by sorry

end SampleCRS.AlmostGreedy
