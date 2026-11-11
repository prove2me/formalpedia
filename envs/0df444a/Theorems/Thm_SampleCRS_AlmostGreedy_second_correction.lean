-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_second_correction
-- name    : SampleCRS.AlmostGreedy.second_correction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:15.737644+00:00
-- url     : https://prove2.me/theorems/02877075-6633-4dd6-a121-4a71c272445f
-- title:
--   §4.1, p.16: the second correction identity
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ satisfy $\sum_jp_j=k$, and fix $i$ with $p_i>0$. Let $X_j$ be independent Bernoulli variables of biases $p_j$, and put $S_{-i}=\sum_{j\ne i}X_j$. Write $C_i$ for Algorithm 4's conditional acceptance probability, averaging its independent samples, coin and uniformly random order.
--   Both equivalent identities in the display hold:
--   $$\mathbb E[\mathrm{AR}_k(S_{-i})]=\Pr[S_{-i}\le k-2]+k\mathbb E\!\left[\frac{\mathbf1_{\{S_{-i}\ge k-1\}}}{S_{-i}+1}\right],$$
--   $$k\mathbb E\!\left[\frac{\mathbf1_{\{S_{-i}\ge k-1\}}}{S_{-i}+1}\right]=\mathbb E[\mathrm{AR}_k(S_{-i})]-\Pr[S_{-i}\le k-2].$$
--
--   These identities preserve the correction at the first possible acceptance rank. At $k=1$, the event $S_{-i}\le-1$ is empty. The two displayed equalities are asserted together.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: independent Bernoulli online activations and their expectations → finite sums weighted by the published product Bernoulli success-set weight; reason: the sums enumerate exactly the same product law, including zero and unit biases
--   - encoding: the event S_{−i} ≤ k−2 → an inequality in ℤ after casting the nonnegative count and k; reason: the event must be empty at k = 1 rather than use truncated natural subtraction
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, first display, p.16

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- The two equivalent identities at the top of p.16; integer thresholds retain k=1. -/
theorem second_correction (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ))
    (i : Fin n) (hi : 0 < p i) :
    activationE p (fun X => StaticProphetSec.AR k (otherCount X i)) =
      activationE p (fun X => if (otherCount X i : ℤ) ≤ (k : ℤ) - 2 then 1 else 0) +
      (k : ℝ) * activationE p (fun X => if k - 1 ≤ otherCount X i then
        1 / ((otherCount X i : ℝ) + 1) else 0) ∧
    (k : ℝ) * activationE p (fun X => if k - 1 ≤ otherCount X i then
      1 / ((otherCount X i : ℝ) + 1) else 0) =
      activationE p (fun X => StaticProphetSec.AR k (otherCount X i)) -
      activationE p (fun X => if (otherCount X i : ℤ) ≤ (k : ℤ) - 2 then 1 else 0) := by sorry

end SampleCRS.AlmostGreedy
