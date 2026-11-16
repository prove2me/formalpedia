-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_4_2
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:52.820607+00:00
-- url     : https://prove2.me/theorems/21bb6f5e-9843-49a4-9d54-bb7e74cb68f5
-- title:
--   Theorem 4.2 — Count Test feasibility and explicit balance
-- statement:
--   For every capacity $k\ge1$, integer $r\ge1$ and unknown $p\in[0,1]^n$ with $\sum_i p_i\le k$, run Count Test (Algorithm 5) in fixed adversarial order. Its output is an active subset of size at most $k$ for every realization of the samples, activations, allowance $R$ and valid selected candidate-slot subset. For each $i$ with $p_i>0$,
--   $$C_i\ge1-\frac1{r+1}-\frac r{2k}-\frac1{2\sqrt k}.$$
--   All integer choices of $r\ge1$ are retained. The experiment uses the exact equivalent uniform-slot implementation on p.19.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: the sequential fraction (min(k,N)-A)/(N-C) in Algorithm 5 → a uniform min(k,N)-subset of N candidate slots chosen in advance; reason: p.19 explicitly proves the two online laws equivalent; unobserved terminal slots are unused and the empty choice at N=0 is unique
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 4.2, p. 18

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_countTest

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem 4.2, p.18. Count Test feasibility and explicit balance. -/
theorem theorem_4_2 {n : ℕ} (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) ≤ (k : ℝ)) :
    CountFeasible n k r ∧ ∀ i, 0 < p i →
      1 - 1 / ((r : ℝ) + 1) - (r : ℝ) / (2 * (k : ℝ)) -
        1 / (2 * Real.sqrt (k : ℝ)) ≤ countC k r p i := by sorry

end SampleCRS.AlmostGreedy.Supplement
