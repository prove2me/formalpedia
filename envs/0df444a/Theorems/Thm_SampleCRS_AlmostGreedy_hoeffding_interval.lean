-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_hoeffding_interval
-- name    : SampleCRS.AlmostGreedy.hoeffding_interval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:32.463824+00:00
-- url     : https://prove2.me/theorems/910a0f80-d6da-4c4e-a58c-cbe2daa7f8fc
-- title:
--   Hoeffding [22, Theorem 5]: integer intervals containing the mean
-- statement:
--   Let $N\ge0$ and $k\ge1$ be integers. Let $q\in[0,1]^N$ satisfy $\sum_jq_j=k$ (which forces $N\ge k\ge1$, so $k/N\le1$), let $D_q$ be the sum of independent Bernoulli variables with these biases, and let $B_N\sim\mathrm{Bin}(N,k/N)$. For all integer endpoints $b,c$ satisfying $b\le k\le c$,
--   $$\Pr[b\le D_q\le c]\ge\Pr[b\le B_N\le c].$$
--
--   This is precisely the integer-mean interval minimization invoked by the authors. It includes negative left endpoints and right endpoints beyond $N$; the support of each law handles those cases. It is a target to be proved, rather than a hypothesis of the mission goal.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: probabilities of integer intervals under independent Bernoulli sums → pbE of the interval indicator with integer endpoints; reason: the published counting formula enumerates the whole law; Σ q = k ≥ 1 forces N ≥ 1, so k/N is defined
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, invocation of Hoeffding [22, Theorem 5], p.17

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- Hoeffding [22, Theorem 5], exactly the integer-mean interval assertion invoked on p.17. -/
theorem hoeffding_interval (N k : ℕ) (hk : 1 ≤ k)
    (q : Fin N → ℝ) (hq : ∀ j, q j ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ j, q j = (k : ℝ)) (b c : ℤ) (hb : b ≤ (k : ℤ)) (hc : (k : ℤ) ≤ c) :
    StaticProphetSec.pbE (fun s => if b ≤ (s : ℤ) ∧ (s : ℤ) ≤ c then 1 else 0)
      (fun _ : Fin N => (k : ℝ) / (N : ℝ)) ≤
    StaticProphetSec.pbE (fun s => if b ≤ (s : ℤ) ∧ (s : ℤ) ≤ c then 1 else 0) q := by sorry

end SampleCRS.AlmostGreedy
