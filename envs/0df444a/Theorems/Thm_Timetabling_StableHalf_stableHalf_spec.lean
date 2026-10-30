-- Prove2me | Theorems.Thm_Timetabling_StableHalf_stableHalf_spec
-- name    : Timetabling.StableHalf.stableHalf_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:23.731048+00:00
-- url     : https://prove2.me/theorems/feeb09cc-7d8c-402f-80bc-8eff36513ada
-- title:
--   Remark: $O(n^2)$ algorithm for a stable set of $|X|/2$ nodes
-- statement:
--   There is an absolute constant $C$ with the following property. Let $q, n \ge 0$, let $G = (X, E)$ be a graph on $X = \{x_1, \bar x_1, \dots, x_n, \bar x_n\}$ containing the perfect matching $\{x_j, \bar x_j\}$, and let $\mathrm{adj}$ be an oracle answering the adjacency of $G$ at a cost of at most $q$ ticks per query. Run the limited backtracking $\mathsf{stableHalf}(\mathrm{adj})$ from tick $0$, with result $\mathrm{res}$ and final tick count $\mathrm{cost}$. Then
--
--   1. if $\mathrm{res} = c$, the nodes $(j, c_j)$, $j = 1, \dots, n$, form a stable set of $|X|/2 = n$ nodes of $G$;
--   2. $\mathrm{res}$ is *failure* if and only if $G$ has no stable set of $n$ nodes;
--   3. $$\mathrm{cost} \le C\,(q+1)\,(n^2+1).$$
--
--   With a unit-cost adjacency test ($q = 1$) this is the Remark: an $O(n^2)$ algorithm deciding whether a graph with a perfect matching has a stable set of $|X|/2$ nodes, and finding one.
--
--   Differences from the source:
--   - generalization: unit-cost adjacency test → an oracle costing at most q ticks per query, bound C(q+1)(n^2+1); reason: specializes to the Remark at q = 1; the CT4 algorithm uses an oracle of constant cost q₀
--   - reading: a graph G = (X, E) with a perfect matching → the matching {(j, true), (j, false)} is given, as the labelling of X = Fin n × Bool; reason: the proof's algorithm decides on matched pairs and cannot run without the matching; finding a perfect matching of a general graph in O(n^2) is not known
--   - encoding: the reverse decision is examined after the decision fails → the two trials of a decision run interleaved, one step each (trialPair); reason: the page does not order the two trials' steps; decisions, implications, reversal, permanence and the stop rule are the paper's
--   - encoding: O(n^2) time; stable set of |X|/2 nodes → tick count ≤ C (q+1)(n^2+1) with C absolute; IsNIndepSet n with n = |X|/2; reason: unit-cost RAM model; the +1 covers n = 0
-- source:
--   de Werra (1985), Remark, p. 155, and proof of Proposition 2.4, p. 155, "It is not difficult to see that since we backtrack only to the last decision, there is an O(n^2) algorithm to solve the problem.". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_stableHalf

namespace Timetabling.StableHalf

/-- **Remark: an `O(n^2)` algorithm for a stable set of `|X|/2` nodes.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Remark, p. 155: "The above proof in
fact says that there is an O(n^2) algorithm to determine whether for a graph G = (X, E) with a
perfect matching, there is a stable set of |X|/2 nodes." Proof of Proposition 2.4, p. 155: "It is
not difficult to see that since we backtrack only to the last decision, there is an O(n^2)
algorithm to solve the problem."

There is an absolute constant `C` such that for every `q`, `n`, every graph `G` on
`X = Fin n × Bool` containing the perfect matching `{(j, true), (j, false)}` and every adjacency
oracle `adj` for `G` costing at most `q` ticks per query, the run of `stableHalf adj` from tick
`0`, with result `res` and final tick count `cost`, satisfies

1. if `res = some c`, the nodes `(j, c j)` form an independent set of `n = |X|/2` nodes;
2. `res = none` if and only if `G` has no independent set of `n` nodes;
3. `cost ≤ C (q + 1) (n^2 + 1)`.

With a unit-cost adjacency test (`q = 1`) this is the Remark's `O(n^2)`. -/
theorem stableHalf_spec :
    ∃ C : ℕ, ∀ (q n : ℕ) (G : SimpleGraph (Fin n × Bool)) [DecidableRel G.Adj],
      (∀ j, G.Adj (j, true) (j, false)) →
      ∀ adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool,
      (∀ u w s, ∃ t ≤ q, (adj u w).run s = (decide (G.Adj u w), s + t)) →
      (∀ c, ((stableHalf adj).run 0).1 = some c →
          G.IsNIndepSet n (Finset.univ.image fun j => (j, c j))) ∧
        (((stableHalf adj).run 0).1 = none ↔ ¬ ∃ s, G.IsNIndepSet n s) ∧
        ((stableHalf adj).run 0).2 ≤ C * (q + 1) * (n ^ 2 + 1) := by sorry

end Timetabling.StableHalf
