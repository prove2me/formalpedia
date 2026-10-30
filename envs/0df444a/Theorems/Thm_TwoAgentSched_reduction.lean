-- Prove2me | Theorems.Thm_TwoAgentSched_reduction
-- name    : TwoAgentSched.reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:49:54.734721+00:00
-- url     : https://prove2.me/theorems/8838398d-896f-4a82-b746-42935a1d25a7
-- title:
--   §4: reduction of $1\|f^A_{\max}:f^B_{\max}$ to $1|prec|f_{\max}$
-- statement:
--   Let all processing times be nonnegative and all cost functions nondecreasing on $[0,\infty)$. With the combined costs $f_i$ of the reduction ($f^A_i$ on A-jobs; $\infty$ or $-\infty$ on a B-job according as $f^B_i(t)>Q$ or $f^B_i(t)\le Q$), let $S^*$ be a feasible schedule minimizing
--   $$
--   f_{\max} = \max_{i\in J^A\cup J^B} f_i(C_i)
--   $$
--   over all feasible schedules, with optimal value $f^*_{\max}$. In the paper's words: "With these positions, if a feasible schedule $\sigma^*$ exists solving $1|prec|f_{\max}$ with finite objective function value $f^*_{\max}$, then $\sigma^*$ is also feasible and optimal for $1\|f^A_{\max}:f^B_{\max}\le Q$, and achieves the same optimal objective function value $f^A_{\max}=f^*_{\max}$. Otherwise, if $f_{\max}=\infty$, then no feasible solution exists for the two-agents problem."
--
--   1. If $f^*_{\max} < \infty$, then $S^*$ satisfies $f^B_{\max}\le Q$, its $f^A_{\max}$ is at most that of every feasible schedule satisfying $f^B_{\max}\le Q$, and $f^A_{\max}(S^*) = f^*_{\max}$.
--   2. If $f^*_{\max} = \infty$, no feasible schedule satisfies $f^B_{\max}\le Q$.
--
--   The reduction turns the two-agent problem into the classical single-agent problem solved by Lawler's algorithm.
--
--   Differences from the source:
--   - reading: σ* solving 1|prec|f_max → S* a feasible start-time schedule minimizing combMax over all feasible schedules, with no precedence constraints; reason: the reduction introduces no precedence constraints among J^A ∪ J^B; optimality is over all feasible schedules, as in problem CP
--   - reading: finite objective function value f*_max → combMax < ⊤; reason: for n_A ≥ 1 the value is never −∞, so < ⊤ is finiteness; for n_A = 0 a feasible optimum has value −∞ = f^A_max, which the paper's finite/∞ dichotomy places on the feasible side
--   - encoding: f_i(t) defined for t ≥ 0 → fComb defined for every real t; reason: only completion times of feasible schedules, which are ≥ 0, are evaluated
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
--   - encoding: job sets J^A = {J^A_1, …, J^A_{n_A}}, J^B = {J^B_1, …, J^B_{n_B}} → Job nA nB = Fin nA ⊕ Fin nB (A-jobs inl h, B-jobs inr k); reason: Lean convention; same instances
--   - encoding: a feasible schedule σ, a feasible assignment of starting times on one machine, nonpreemptive, zero release dates → Feasible p S: S j ≥ 0 and, for distinct jobs, S i + p i ≤ S j or S j + p j ≤ S i; completion times S j + p j; reason: the paper's definition written out; zero-length jobs may share a start time
--   - encoding: f^A_max = max_h f^A_h(C^A_h) → fAmax: Finset.sup in EReal, equal to ⊥ when n_A = 0; reason: for n_A ≥ 1 it is the real maximum; the paper never treats an empty agent
--   - encoding: f^B_max ≤ Q → BOk: f^B_k(C^B_k) ≤ Q for every B-job k; reason: equivalent for n_B ≥ 1, written without a max so that n_B = 0 needs no convention (the constraint is then empty)
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 (definition of f_i and the paragraph "With these positions, …")

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax
import Definitions.Def_TwoAgentSched_fComb

namespace TwoAgentSched

/-- **Reduction of `1‖f^A_max : f^B_max` to `1|prec|f_max`** (Agnetis–Mirchandani–Pacciarelli–
Pacifici, Oper. Res. 52(2) (2004), §4, p. 232). With the combined costs `f_i = f^A_i` on A-jobs
and `f_i ∈ {∞, −∞}` on B-jobs according to `f^B_i(t) > Q` or `≤ Q` (`fComb`), let `S*` be a
feasible schedule minimizing `f_max = max_i f_i(C_i)` (`combMax`) over all feasible schedules.
1. If `f_max(S*) < ∞`, then `S*` satisfies `f^B_max ≤ Q`, it is optimal for CP (its `f^A_max`
   is at most that of every feasible schedule satisfying `f^B_max ≤ Q`), and
   `f^A_max(S*) = f_max(S*)`.
2. If `f_max(S*) = ∞`, no feasible schedule satisfies `f^B_max ≤ Q`. -/
theorem reduction {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (Q : ℝ) (hp : ∀ j, 0 ≤ p j) (hfA : ∀ h, MonotoneOn (fA h) (Set.Ici 0))
    (hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0))
    (Sstar : Job nA nB → ℝ) (hSstar : Feasible p Sstar)
    (hopt : ∀ S, Feasible p S →
      combMax fA fB Q (fun j => Sstar j + p j) ≤ combMax fA fB Q (fun j => S j + p j)) :
    (combMax fA fB Q (fun j => Sstar j + p j) < ⊤ →
      BOk fB Q (fun j => Sstar j + p j) ∧
      (∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
        fAmax fA (fun j => Sstar j + p j) ≤ fAmax fA (fun j => S j + p j)) ∧
      fAmax fA (fun j => Sstar j + p j) = combMax fA fB Q (fun j => Sstar j + p j)) ∧
    (combMax fA fB Q (fun j => Sstar j + p j) = ⊤ →
      ¬ ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) := by sorry

end TwoAgentSched
