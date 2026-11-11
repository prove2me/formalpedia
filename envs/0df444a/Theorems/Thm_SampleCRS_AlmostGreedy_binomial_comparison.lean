-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_binomial_comparison
-- name    : SampleCRS.AlmostGreedy.binomial_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:28.105193+00:00
-- url     : https://prove2.me/theorems/ac13734e-806e-44bd-827e-79bac4a1c1f8
-- title:
--   §4.1, p.17: binomial tail and expectation comparison
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ with $\sum_jp_j=k$, and $S=\sum_jX_j$ for independent $X_j\sim\mathrm{Ber}(p_j)$. For every integer $N\ge n$, let $B_N\sim\mathrm{Bin}(N,k/N)$. Then
--   $$\Pr[h_k(S)\ge t]\ge\Pr[h_k(B_N)\ge t]\quad\text{for every }t\in[0,1],\qquad \mathbb E[h_k(S)]\ge\mathbb E[h_k(B_N)].$$
--
--   Both probability comparison and expectation comparison are included. The probability vector for $S$ keeps its original length; adding $N-n$ zero trials leaves its law unchanged. Total mass and the coordinate bounds force $N\ge n\ge k\ge1$.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: expectations of S and B_N, sums of independent Bernoulli trials → the published pbE counting formula, with constant bias k/N for B_N; reason: the count laws coincide, and total mass k with probabilities at most one implies N ≥ n ≥ k ≥ 1
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, tail display and following expectation comparison, p.17

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- The tail and expectation comparisons on p.17, for every N ≥ n. -/
theorem binomial_comparison (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ))
    (N : ℕ) (hN : n ≤ N) :
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      StaticProphetSec.pbE (fun s => if t ≤ h k s then 1 else 0)
        (fun _ : Fin N => (k : ℝ) / (N : ℝ)) ≤
      StaticProphetSec.pbE (fun s => if t ≤ h k s then 1 else 0) p) ∧
    StaticProphetSec.pbE (h k) (fun _ : Fin N => (k : ℝ) / (N : ℝ)) ≤
      StaticProphetSec.pbE (h k) p := by sorry

end SampleCRS.AlmostGreedy
