-- Prove2me | Theorems.Thm_TwoAgentSched_lawler_spec
-- name    : TwoAgentSched.lawler_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:50:33.612987+00:00
-- url     : https://prove2.me/theorems/0172b0c2-a06a-4a2e-be75-02acc840c094
-- title:
--   Lawler (1973): $1|prec|f_{\max}$ in $O(n^2)$ time
-- statement:
--   There is an absolute constant $C$ such that the following holds for every $n$, every linearly ordered set of cost values, all nonnegative processing times $p_1,\dots,p_n$, all cost functions $g_1,\dots,g_n$ nondecreasing on $[0,\infty)$, and every acyclic precedence relation $\to$ on the jobs (no chain $i\to\dots\to i$). Lawler's algorithm
--
--   1. returns a sequence $\sigma$;
--   2. $\sigma$ contains every job exactly once, respects the precedences ($i\to j$ implies $i$ before $j$), and is optimal for $1|prec|f_{\max}$:
--   $$
--   \max_j g_j\bigl(C_j(\sigma)\bigr) \le \max_i g_i\bigl(S_i + p_i\bigr)
--   $$
--   for every feasible schedule $S$ respecting the precedences ($S_i + p_i \le S_j$ whenever $i \to j$);
--   3. performs at most $C\, n^2$ unit-cost steps.
--
--   The paper cites this result and uses it through the reduction of §4.
--
--   Differences from the source:
--   - generalization: real-valued (or extended-real) costs f_i → costs in any linearly ordered type β; reason: β = EReal, the instance the reduction needs, and β = ℝ are instances
--   - reading: Lawler's O(n^2) time algorithm → the timed implementation lawler (successor counts, first minimizing eligible job); reason: the cited algorithm, with the usual successor-count bookkeeping that gives O(n^2)
--   - reading: optimal for 1|prec|f_max → every job's cost in σ is at most some job's cost in every precedence-respecting feasible schedule S (∀ j, ∃ i, g j (C_j(σ)) ≤ g i (S i + p i)); reason: equivalent to max_j g_j(C_j(σ)) ≤ max_i g_i(C_i(S)) without needing a maximum of an empty family
--   - encoding: precedence constraints → prec : Fin n → Fin n → Prop, decidable and acyclic (¬ TransGen prec i i); S respects it when prec i j → S i + p i ≤ S j; σ respects it when no job precedes an earlier one; reason: the standard meaning of a precedence relation on a single machine
--   - reading: time, assuming each f^A_h(·) value can be computed in constant time and the deadlines are available (p. 233) → the cost of the Timed run: one step per real addition or subtraction, per comparison (reals, cuts), per evaluation f^A_h(t), per deadline lookup, per list cell traversed, consed or moved, per relation query or array access; reason: the unit-cost RAM model with the paper's constant-time assumptions; the deadlines are an input, as in the paper's case where f^B_k^{-1} is available
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - encoding: a feasible schedule σ, a feasible assignment of starting times on one machine, nonpreemptive, zero release dates → Feasible p S: S j ≥ 0 and, for distinct jobs, S i + p i ≤ S j or S j + p j ≤ S i; completion times S j + p j; reason: the paper's definition written out; zero-length jobs may share a start time
--   - encoding: a sequence, each job started as soon as the previous one is completed → a duplicate-free list σ of all jobs (IsSeq) with completion times seqC p σ j = sum of p over the prefix of σ ending at j; reason: the no-idle schedule of a sequence written out
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 ("For the latter problem, Lawler (1973) devises an O(n^2) time algorithm"), citing E. L. Lawler, Optimal sequencing of a single machine subject to precedence constraints, Management Sci. 19 (1973) 544–546

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_lawler

namespace TwoAgentSched

/-- **Lawler's `O(n²)` algorithm for `1|prec|f_max`** (Lawler 1973, as cited in Agnetis–
Mirchandani–Pacciarelli–Pacifici, Oper. Res. 52(2) (2004), §4, p. 232: "Lawler (1973) devises an
O(n²) time algorithm").

There is one absolute constant `C` such that for every `n`, every linearly ordered cost type `β`,
nonnegative processing times `p`, costs `g j` nondecreasing on `[0, ∞)`, and every acyclic
precedence relation `prec` (`prec i j`: `i` before `j`; no chain of precedences returns to its
start), the run
`lawler p g prec`
1. returns a sequence;
2. that sequence contains every job once, respects `prec`, and is optimal: for every feasible
   schedule `S` respecting `prec` (`S i + p i ≤ S j` whenever `prec i j`), each job's cost
   `g j (C_j)` in the sequence is at most some job's cost `g i (S i + p i)` in `S`, i.e.
   `max_j g_j(C_j(σ)) ≤ max_i g_i(C_i(S))`;
3. costs at most `C · n²` unit steps. -/
theorem lawler_spec :
    ∃ C : ℝ, ∀ (n : ℕ) (β : Type) [LinearOrder β] (p : Fin n → ℝ) (g : Fin n → ℝ → β)
      (prec : Fin n → Fin n → Prop) [DecidableRel prec],
      (∀ i, ¬ Relation.TransGen prec i i) → (∀ j, 0 ≤ p j) → (∀ j, MonotoneOn (g j) (Set.Ici 0)) →
      (∃ σ, (lawler p g prec).val = some σ) ∧
      (∀ σ, (lawler p g prec).val = some σ →
        IsSeq σ ∧ σ.Pairwise (fun a b => ¬ prec b a) ∧
        ∀ S : Fin n → ℝ, Feasible p S → (∀ i j, prec i j → S i + p i ≤ S j) →
          ∀ j, ∃ i, g j (seqC p σ j) ≤ g i (S i + p i)) ∧
      ((lawler p g prec).cost : ℝ) ≤ C * (n : ℝ) ^ 2 := by sorry

end TwoAgentSched
