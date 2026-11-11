-- Prove2me | Theorems.Thm_RoundedPotentials_Main_lemma_3_1
-- name    : RoundedPotentials.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:01.500203+00:00
-- url     : https://prove2.me/theorems/d084c2b8-17e0-405b-8101-b1d504c36aff
-- title:
--   Lemma 3.1 — a lower bound from approximate conservation
-- statement:
--   Let a loopless directed network have $n$ vertices and nonnegative integer capacities. Let $s\ne t$, let $N\ge n$ be an integer, and let $p\ge0$ be an integer. If a capacity-feasible assignment $g$ satisfies
--   $$|\operatorname{ex}_g(v)-p(1[v=s]-1[v=t])|\le\frac1{8N}\quad(v\in V),$$
--   then some exact $st$-flow has real value at least $p$.
--
--   This is the full lower-bound conclusion $\operatorname{MaxFlow}(s,t)\ge p$, expressed by an attained feasible flow rather than only a cut inequality. The theorem does not require the capacity upper bound to be positive.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: MaxFlow(s,t) ≥ p → there exists a published IsFlow of value at least p; reason: finite nonnegative networks attain their maximum by eq. (5); this states the flow lower bound itself
--   - generalization: §3 fixes an upper capacity bound W ≥ 1 → no lower bound on W in Lemma 3.1; reason: integrality and approximate conservation are sufficient; W=0 also satisfies the same result
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 13, Lemma 3.1; standing assumptions §2 p.11 and §3 p.13

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main
open scoped BigOperators

theorem lemma_3_1 {n W : ℕ} (I : Instance n W) (s t : Fin n) (hst : s ≠ t)
    (N : ℕ) (hN : n ≤ N) (p : ℤ) (hp : 0 ≤ p) (g : Assignment n)
    (hg : CapacityFeasible I g)
    (herr : ∀ v, |excess g v - target s t (p : ℝ) v| ≤ epsilon N) :
    ∃ (f : Assignment n) (value : ℝ),
      FlowsNetworks.MaxFlow.IsFlow (network I) s t f value ∧ (p : ℝ) ≤ value := by sorry

end RoundedPotentials.Main
