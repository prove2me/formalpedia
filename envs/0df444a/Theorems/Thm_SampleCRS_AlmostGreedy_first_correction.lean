-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_first_correction
-- name    : SampleCRS.AlmostGreedy.first_correction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:29.229076+00:00
-- url     : https://prove2.me/theorems/193cce8f-cf95-4c64-880b-f4c8eafd69a3
-- title:
--   §4.1, p.15: both identities for the final correction term
-- statement:
--   Let $k\ge1$, $p\in[0,1]^n$ satisfy $\sum_jp_j=k$, and fix $i$ with $p_i>0$. Let $X_j$ be independent Bernoulli variables of biases $p_j$, and put $S_{-i}=\sum_{j\ne i}X_j$. Write $C_i$ for Algorithm 4's conditional acceptance probability, averaging its independent samples, coin and uniformly random order.
--   The following chain consists of two equalities:
--   $$k\sum_{j\ne i}p_j\mathbb E\!\left[\frac{X_j\mathbf1_{\{S_{-i}\ge k\}}}{S_{-i}(S_{-i}+1)}\right]=\sum_{j\ne i}p_j\mathbb E[\mathrm{AR}_k(S_{-i}-X_j)-\mathrm{AR}_k(S_{-i})]=\mathbb E[\min\{k,S_{-i}\}]-(k-p_i)\mathbb E[\mathrm{AR}_k(S_{-i})].$$
--   The zero-denominator convention is the same as in (4).
--
--   The result expresses the positive correction entirely through functions of the count. Subtraction $S_{-i}-X_j$ is nonnegative for every summand, since $j\ne i$.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: independent Bernoulli online activations and their expectations → finite sums weighted by the published product Bernoulli success-set weight; reason: the sums enumerate exactly the same product law, including zero and unit biases
--   - encoding: the final fraction in (4) is zero at S_{−i} = 0 → real division by zero equals zero; reason: this implements exactly the stated convention
--   - encoding: the two equalities of a displayed chain → a conjunction of both equalities; reason: both clauses are asserted, with no conclusion omitted
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, final display, p.15

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- Both equalities in the correction-term display, p.15. -/
theorem first_correction (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ))
    (i : Fin n) (hi : 0 < p i) :
    (k : ℝ) * (∑ j ∈ Finset.univ.erase i, p j * activationE p (fun X =>
      (if X j = true ∧ k ≤ otherCount X i then 1 else 0) /
        ((otherCount X i : ℝ) * ((otherCount X i : ℝ) + 1)))) =
      (∑ j ∈ Finset.univ.erase i, p j * activationE p (fun X =>
        StaticProphetSec.AR k (otherCount X i - (if X j = true then 1 else 0)) -
          StaticProphetSec.AR k (otherCount X i))) ∧
    (∑ j ∈ Finset.univ.erase i, p j * activationE p (fun X =>
      StaticProphetSec.AR k (otherCount X i - (if X j = true then 1 else 0)) -
        StaticProphetSec.AR k (otherCount X i))) =
      activationE p (fun X => min (k : ℝ) (otherCount X i : ℝ)) -
        ((k : ℝ) - p i) * activationE p (fun X => StaticProphetSec.AR k (otherCount X i)) := by sorry

end SampleCRS.AlmostGreedy
