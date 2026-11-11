-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_eq_4
-- name    : SampleCRS.AlmostGreedy.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:20.025885+00:00
-- url     : https://prove2.me/theorems/922c1409-06df-46ae-b8f2-a87c4f84cfcc
-- title:
--   §4.1, equation (4): exact acceptance identity
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ satisfy $\sum_jp_j=k$, and fix $i$ with $p_i>0$. Let $X_j$ be independent Bernoulli variables of biases $p_j$, and put $S_{-i}=\sum_{j\ne i}X_j$. Write $C_i$ for Algorithm 4's conditional acceptance probability, averaging its independent samples, coin and uniformly random order.
--   Then
--   $$C_i=\mathbb E[\mathrm{AR}_k(S_{-i})]-\frac{kp_i}{2k+1}\mathbb E\!\left[\frac{\mathbf1_{\{S_{-i}\ge k-1\}}}{S_{-i}+1}\right]+\frac{k}{2k+1}\sum_{j\ne i}p_j\mathbb E\!\left[\frac{X_j\mathbf1_{\{S_{-i}\ge k\}}}{S_{-i}(S_{-i}+1)}\right].$$
--   The last fraction is zero when $S_{-i}=0$.
--
--   This identity relates the algorithm to the greedy acceptance rate while retaining the joint dependence of $X_j$ and the count. It is an equality, with both correction terms and their exact coefficients.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: independent Bernoulli online activations and their expectations → finite sums weighted by the published product Bernoulli success-set weight; reason: the sums enumerate exactly the same product law, including zero and unit biases
--   - encoding: C_i is conditional on X_i = 1 and averages samples, order and internal randomness → the joint accepted-and-active weight divided by p_i, with one independent coin drawn up front; reason: p_i > 0 and the coin is used at most once, so this is the same conditional probability
--   - encoding: the final fraction in (4) is zero at S_{−i} = 0 → real division by zero equals zero; reason: this implements exactly the stated convention
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, eq. (4), p.15

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- Exact conditional acceptance probability, equation (4), p.15. -/
theorem eq_4 (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ))
    (i : Fin n) (hi : 0 < p i) :
    conditionalAcceptance k p i =
      activationE p (fun X => StaticProphetSec.AR k (otherCount X i)) -
      ((k : ℝ) * p i / (2 * (k : ℝ) + 1)) *
        activationE p (fun X => if k - 1 ≤ otherCount X i then
          1 / ((otherCount X i : ℝ) + 1) else 0) +
      ((k : ℝ) / (2 * (k : ℝ) + 1)) *
        ∑ j ∈ Finset.univ.erase i, p j * activationE p (fun X =>
          (if X j = true ∧ k ≤ otherCount X i then 1 else 0) /
            ((otherCount X i : ℝ) * ((otherCount X i : ℝ) + 1))) := by sorry

end SampleCRS.AlmostGreedy
