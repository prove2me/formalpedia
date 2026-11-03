-- Prove2me | Theorems.Thm_SubsetSum_MITM_Race_bound
-- name    : SubsetSum.MITM.Race.bound
-- status  : Open
-- author  : @darkhipo
-- created : 2026-11-02T06:18:08.686376+00:00
-- url     : https://prove2.me/theorems/0fbd19fd-2d36-4f5d-8de6-df8f4f2c94d6
-- title:
--   Subset Sum in $O(2^{n/2})$ word-RAM steps (poly-free, $\alpha = 1/2$)
-- statement:
--   There is one finite deterministic program for the Big O Speedrun subset-sum model that decides every instance with $n \ge 2$ and runs in
--   $$T(n) = C\cdot 2^{\lceil n/2 \rceil} + D n$$
--   steps, so that $T(n)^2 \le K\,2^n$ for every $n \ge 2$ with a single $K$. This is $\alpha = 1/2$ **exactly**: no polynomial factor, hence strictly better than the classic bound $O^*(2^{n/2})$ of Horowitz and Sahni (1974), whose $n\cdot\mathrm{poly}(n)$ probe cost squares to $2^n\,\mathrm{poly}(n)^2$ and so does **not** satisfy the definition at $\alpha = 1/2$.
--
--   **Why the polynomial must vanish.** At $\alpha = 1/2$ the definition reads $T(n)^2 \le K 2^n$ with no threshold and no slack, so any $\mathrm{poly}(n)$ factor in $T$ squares to an unbounded factor on $2^n$. Sorted meet-in-the-middle with binary-search probes, radix sorting on half-word digits, and any per-subset bit extraction are therefore unlistable at $1/2$ in this model.
--
--   **The construction.** Both halves' subset sums are built by doubling merge (a geometric sum, $\sum_k 2^k \le 2^{h+1}$) rather than sorted from scratch, and complements are found by a single linear two-pointer sweep over the two sorted arrays: on $S_1[i] + S_2[j] < t$ increment $i$, on $> t$ decrement $j$, on equality accept. Each step eliminates one row or one column, so the sweep is linear. Every instruction, including the word comparison, costs one step regardless of the input bit length $b$, so the same bound serves every $c$ in $b \le n^c$.
--
--   A second, independent construction reaches the same exponent by direct addressing: mark each left-half sum with one store at $\mathrm{BASE}+s$ and probe with one load at $\mathrm{BASE}+(t-r)$, giving flat cost $\le 84\cdot 2^{\lceil n/2\rceil}$. Both are poly-free; the merge-and-sweep program is the one formalized here.
--
--   The program never draws a random word, so correctness is deterministic although the model is randomized. Proof: 27 modules of core Lean (no Mathlib), about 16,900 lines.
-- source:
--   Statement: https://bigospeedrun.com/subset-sum (target `SolvedInTime (1/2)`). Algorithm: Horowitz & Sahni, "Computing partitions with applications to the knapsack problem", JACM 1974. Proof (kernel-checked, `lake build` 30 jobs / 0 errors / 0 sorry, axioms [propext, Classical.choice, Quot.sound]): https://github.com/darkhipo/subset-sum-half at commit 1224502, module Submission/Prog2Race.lean:389; filed with the board under bigospeedrun/verifier issues #100 and #101.

import Definitions.Def_BigOSpeedrunSubsetSum

theorem SubsetSum.MITM.Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (1 / 2 : Rat) := by sorry
