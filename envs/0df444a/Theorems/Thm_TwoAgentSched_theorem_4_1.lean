-- Prove2me | Theorems.Thm_TwoAgentSched_theorem_4_1
-- name    : TwoAgentSched.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:53:53.538041+00:00
-- url     : https://prove2.me/theorems/eefa3333-8a8c-43cd-a686-d3eb78ab003f
-- title:
--   Theorem 4.1: $1\|f^A_{\max}:f^B_{\max}$ solved in $O(n_A^2+n_B\log n_B)$ time (corrected: cost clause excludes $n_A=0$, $n_B=1$)
-- statement:
--   There is an absolute constant $C$ such that the following holds for all $n_A$, $n_B$, all nonnegative processing times $p$, all cost functions $f^A_h$ and $f^B_k$ nondecreasing on $[0,\infty)$, every real bound $Q$, and deadlines $D^B_k$ (cuts) representing $f^B_k$ and $Q$. Run the §4 algorithm on $p$, $f^A$ and the deadlines.
--
--   1. **(decision)** It returns a schedule if and only if some feasible schedule satisfies $f^B_{\max}\le Q$.
--   2. **(optimality)** If it returns $\sigma$, then $\sigma$ is a sequence of all jobs (processed without idle time it is a feasible schedule), it satisfies $f^B_{\max}\le Q$, and
--   $$
--   f^A_{\max}(\sigma) \le f^A_{\max}(S)
--   $$
--   for every feasible schedule $S$ satisfying $f^B_{\max}\le Q$.
--   3. **(running time)** Unless $n_A=0$ and $n_B=1$, the number of unit-cost steps is at most
--   $$
--   C\cdot\bigl(n_A^2 + n_B\log n_B\bigr).
--   $$
--
--   This is the paper's Theorem 4.1, "$1\|f^A_{\max}:f^B_{\max}$ can be solved in time $O(n_A^2+n_B\log n_B)$", for the algorithm the paper derives from Lawler's rule: sort the B-jobs by deadline, then repeatedly schedule last the unscheduled B-job with the largest deadline if it fits, and otherwise the A-job of least cost. The time is counted with the paper's assumptions: "If we suppose that each $f^A_h(\cdot)$ value can be computed in constant time" and "(If the inverse function $f^{B^{-1}}_k(\cdot)$ is available, the deadlines can be computed in constant time; otherwise this requires logarithmic time.)" The deadlines are given as input.
--
--   **Formalization Note** The theorem is about the paper's own algorithm `cpAlgo`, which is stronger than the existence of some algorithm. Its cost is the cost of the same run whose result clauses 1 and 2 describe. The algorithm reads agent $B$ only through the deadlines.
--
--   Differences from the source:
--   - correction: running time O(n_A^2 + n_B log n_B) for every n_A, n_B → the cost bound unless n_A = 0 and n_B = 1; clauses 1 and 2 hold for every n_A, n_B; reason: counterexample: n_A = 0, n_B = 1, p = 1, Q = 0: with f^B ≡ 0 the instance is feasible and with f^B ≡ 1 it is not, so the algorithm must compare the deadline (cost ≥ 1), while n_A^2 + n_B log n_B = 0 + 1 · log 1 = 0; at n_A = n_B = 0 the algorithm costs 0 and the bound holds
--   - reading: can be solved → (1) the algorithm returns a schedule iff some feasible schedule satisfies f^B_max ≤ Q; (2) a returned sequence satisfies f^B_max ≤ Q and has f^A_max at most that of every feasible start-time schedule satisfying it; reason: problem CP (p. 232): find σ* with f^B(σ*) ≤ Q and f^A(σ*) minimum, and recognize infeasible instances (p. 232: 'the instance is not feasible')
--   - reading: 1‖f^A_max : f^B_max can be solved in that time → the §4 algorithm cpAlgo (largest-deadline B-job first, first minimizing A-job) runs in that time; reason: the theorem concludes the paper's analysis of this algorithm ('we may conclude with the following'); a statement about it implies the existence of an algorithm
--   - reading: time, assuming each f^A_h(·) value can be computed in constant time and the deadlines are available (p. 233) → the cost of the Timed run: one step per real addition or subtraction, per comparison (reals, cuts), per evaluation f^A_h(t), per deadline lookup, per list cell traversed, consed or moved, per relation query or array access; reason: the unit-cost RAM model with the paper's constant-time assumptions; the deadlines are an input, as in the paper's case where f^B_k^{-1} is available
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
--   - generalization: a real deadline D^B_k with f^B_k(C) ≤ Q for C ≤ D^B_k and f^B_k(C) > Q for C > D^B_k → a cut D k : WithTop (ℝ ×ₗ Bool) with f^B_k(t) ≤ Q ↔ (t, true) ≤ D k for t ≥ 0 (IsDeadline); reason: the paper's real deadline need not exist (f = 0 on [0, 1) and 1 after, Q = 0); when it exists, (D^B_k, true) is such a cut (deadline_exists), so the statement specializes to the paper's
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
--   - encoding: job sets J^A = {J^A_1, …, J^A_{n_A}}, J^B = {J^B_1, …, J^B_{n_B}} → Job nA nB = Fin nA ⊕ Fin nB (A-jobs inl h, B-jobs inr k); reason: Lean convention; same instances
--   - encoding: a feasible schedule σ, a feasible assignment of starting times on one machine, nonpreemptive, zero release dates → Feasible p S: S j ≥ 0 and, for distinct jobs, S i + p i ≤ S j or S j + p j ≤ S i; completion times S j + p j; reason: the paper's definition written out; zero-length jobs may share a start time
--   - encoding: a sequence, each job started as soon as the previous one is completed → a duplicate-free list σ of all jobs (IsSeq) with completion times seqC p σ j = sum of p over the prefix of σ ending at j; reason: the no-idle schedule of a sequence written out
--   - encoding: f^A_max = max_h f^A_h(C^A_h) → fAmax: Finset.sup in EReal, equal to ⊥ when n_A = 0; reason: for n_A ≥ 1 it is the real maximum; the paper never treats an empty agent
--   - encoding: f^B_max ≤ Q → BOk: f^B_k(C^B_k) ≤ Q for every B-job k; reason: equivalent for n_B ≥ 1, written without a max so that n_B = 0 needs no convention (the constraint is then empty)
--   - encoding: J^B ordered in nondecreasing order of deadlines, the largest unscheduled one considered → J^B sorted in nondecreasing order of the reversed order on deadlines, consumed from the front; reason: the same order read from the other end
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), Theorem 4.1, p. 233, for the algorithm of §4, pp. 232–233

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax
import Definitions.Def_TwoAgentSched_IsDeadline
import Definitions.Def_TwoAgentSched_cpAlgo

namespace TwoAgentSched

/-- **Theorem 4.1** (Agnetis–Mirchandani–Pacciarelli–Pacifici, *Scheduling Problems with Two
Competing Agents*, Oper. Res. 52(2) (2004), p. 233: "`1‖f^A_max : f^B_max` can be solved in time
`O(n_A² + n_B log n_B)`"), for the paper's own algorithm of §4 (pp. 232–233), `cpAlgo`; this is
stronger than the existence of some algorithm.

There is one absolute constant `C`, chosen before everything else, such that for all `n_A`,
`n_B`, nonnegative processing times `p`, cost functions `f^A_h`, `f^B_k` nondecreasing on
`[0, ∞)`, every real bound `Q`, and deadlines `D k` representing `f^B_k` and `Q` (cuts, see
`IsDeadline`; the algorithm reads agent B only through them), the run `cpAlgo p fA D`
(A) reports a schedule iff some feasible schedule satisfies `f^B_max ≤ Q`;
(B) when it returns `σ`, `σ` is a sequence of all jobs (a feasible schedule without idle time,
    `seqC_feasible`) satisfying `f^B_max ≤ Q`, and its `f^A_max` is at most that of every
    feasible schedule satisfying `f^B_max ≤ Q`;
(Cost) unless `n_A = 0` and `n_B = 1` (where the printed bound is `0`), it uses at most
    `C · (n_A² + n_B log n_B)` unit-cost steps. -/
theorem theorem_4_1 :
    ∃ C : ℝ, ∀ (nA nB : ℕ) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
      (Q : ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool)),
      (∀ j, 0 ≤ p j) → (∀ h, MonotoneOn (fA h) (Set.Ici 0)) →
      (∀ k, MonotoneOn (fB k) (Set.Ici 0)) → (∀ k, IsDeadline (fB k) Q (D k)) →
      (((cpAlgo p fA D).val.isSome = true) ↔
          ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) ∧
      (∀ σ, (cpAlgo p fA D).val = some σ →
        IsSeq σ ∧ BOk fB Q (seqC p σ) ∧
        ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
          fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j)) ∧
      (¬ (nA = 0 ∧ nB = 1) →
        ((cpAlgo p fA D).cost : ℝ) ≤
          C * ((nA : ℝ) ^ 2 + (nB : ℝ) * Real.log (nB : ℝ))) := by sorry

end TwoAgentSched
