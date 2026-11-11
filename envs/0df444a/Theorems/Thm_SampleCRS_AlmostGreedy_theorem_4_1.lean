-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_theorem_4_1
-- name    : SampleCRS.AlmostGreedy.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:24.501415+00:00
-- url     : https://prove2.me/theorems/58fc6bb9-329a-4f38-aa63-71585b54a5c9
-- title:
--   Theorem 4.1: feasibility and exact balance of Almost-Greedy
-- statement:
--   For every ground-set size $n$, every integer capacity $k\ge1$, and every unknown activation vector $p\in[0,1]^n$ with $\sum_jp_j=k$, run the defined Algorithm 4 with independent online activations $X_j\sim\mathrm{Ber}(p_j)$, independent samples $Y_j\sim\mathrm{Ber}(p_j)$, independent uniform arrival order and its independent coin of bias $(k+1)/(2k+1)$. The algorithm always accepts at most $k$ elements, for every realization. For every element $i$ with $p_i>0$,
--   $$C_i=\Pr[i\text{ accepted}\mid X_i=1]\ge\gamma_k=1-e^{-k}\frac{k^k}{k!}.$$
--
--   The theorem asserts both clauses together for every capacity and every probability vector of total mass $k$. The run takes only capacity, arrivals, activations, samples and the coin; its law is parameterized by $p$, but its decisions never read $p$. The balance guarantee averages all four sources of randomness, while feasibility holds even on zero-probability realizations.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
--   - encoding: C_i is conditional on X_i = 1 and averages samples, order and internal randomness → the joint accepted-and-active weight divided by p_i, with one independent coin drawn up front; reason: p_i > 0 and the coin is used at most once, so this is the same conditional probability
--   - encoding: the exact constant 1−exp(−k)k^k/k! → the published definition StaticProphetSec.gamma k; reason: its body is precisely the displayed real exponential-factorial expression
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 4.1, p.14; standing capacity convention §2, p.5

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_experiment
import Definitions.Def_SampleCRS_AlmostGreedy_h
import Definitions.Def_StaticProphetSec_pbE
import Definitions.Def_StaticProphetSec_poisE
import Definitions.Def_StaticProphetSec_gamma

namespace SampleCRS.AlmostGreedy

/-- Theorem 4.1, p.14: pathwise feasibility and exact conditional balance, for all capacities. -/
theorem theorem_4_1 (n k : ℕ) (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, p j = (k : ℝ)) :
    (∀ (σ : Equiv.Perm (Fin n)) (X Y : Fin n → Bool) (Q : Bool),
      (run k σ X Y Q).card ≤ k) ∧
    (∀ i : Fin n, 0 < p i → StaticProphetSec.gamma k ≤ conditionalAcceptance k p i) := by sorry

end SampleCRS.AlmostGreedy
