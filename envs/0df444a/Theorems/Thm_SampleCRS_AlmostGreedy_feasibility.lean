-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_feasibility
-- name    : SampleCRS.AlmostGreedy.feasibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:11.270205+00:00
-- url     : https://prove2.me/theorems/396afa4b-6563-4841-b41c-8f91de7d0168
-- title:
--   Theorem 4.1: pathwise feasibility clause
-- statement:
--   For every $n$ and integer capacity $k\ge1$, every arrival permutation $\sigma$, every online activation vector $X$, every sample vector $Y$, and either value of the coin $Q$, Algorithm 4's defined run satisfies
--   $$|\operatorname{run}(k,\sigma,X,Y,Q)|\le k.$$
--
--   This is the pathwise feasibility clause of Theorem 4.1. It requires no distributional assumptions, because it holds for every realization, including realizations of probability zero.
--
--   Differences from the source:
--   - encoding: the labeled set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling preserves each element and its arrival rank
--   - encoding: the standing assumption k ≥ 1 in §2, p.5 → an explicit hypothesis 1 ≤ k; reason: Lean natural numbers include zero
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 4.1, p.14 (feasibility clause)

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_run

namespace SampleCRS.AlmostGreedy

/-- The pathwise feasibility clause of Theorem 4.1, p.14. -/
theorem feasibility (n k : ℕ) (hk : 1 ≤ k) :
    ∀ (σ : Equiv.Perm (Fin n)) (X Y : Fin n → Bool) (Q : Bool),
      (run k σ X Y Q).card ≤ k := by sorry

end SampleCRS.AlmostGreedy
