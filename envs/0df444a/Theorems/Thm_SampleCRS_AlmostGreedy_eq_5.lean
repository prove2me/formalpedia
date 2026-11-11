-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_eq_5
-- name    : SampleCRS.AlmostGreedy.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:32.793243+00:00
-- url     : https://prove2.me/theorems/3713c3b8-36a5-4822-916c-4c6a76744118
-- title:
--   §4.1, equation (5): acceptance via h
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ satisfy $\sum_jp_j=k$, and fix $i$ with $p_i>0$. Let $X_j$ be independent Bernoulli variables of biases $p_j$, and put $S_{-i}=\sum_{j\ne i}X_j$. Write $C_i$ for Algorithm 4's conditional acceptance probability, averaging its independent samples, coin and uniformly random order.
--   With $h_k(s)=((k+1)\mathrm{AR}_k(s)+\min\{k,s\})/(2k+1)$,
--   $$C_i=\mathbb E[h_k(S_{-i})]+\frac{p_i}{2k+1}\Pr[S_{-i}\le k-2].$$
--
--   This is the exact expression used for comparison with the unconditioned active count. Its second term is present at every capacity, with an empty event when $k=1$.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: independent Bernoulli online activations and their expectations → finite sums weighted by the published product Bernoulli success-set weight; reason: the sums enumerate exactly the same product law, including zero and unit biases
--   - encoding: C_i is conditional on X_i = 1 and averages samples, order and internal randomness → the joint accepted-and-active weight divided by p_i, with one independent coin drawn up front; reason: p_i > 0 and the coin is used at most once, so this is the same conditional probability
--   - encoding: the event S_{−i} ≤ k−2 → an inequality in ℤ after casting the nonnegative count and k; reason: the event must be empty at k = 1 rather than use truncated natural subtraction
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, eq. (5), p.16

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- Equation (5), p.16. -/
theorem eq_5 (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ))
    (i : Fin n) (hi : 0 < p i) :
    conditionalAcceptance k p i = activationE p (fun X => h k (otherCount X i)) +
      p i / (2 * (k : ℝ) + 1) *
        activationE p (fun X => if (otherCount X i : ℤ) ≤ (k : ℤ) - 2 then 1 else 0) := by sorry

end SampleCRS.AlmostGreedy
