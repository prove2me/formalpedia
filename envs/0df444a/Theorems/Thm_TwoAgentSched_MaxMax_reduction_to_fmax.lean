-- Prove2me | Theorems.Thm_TwoAgentSched_MaxMax_reduction_to_fmax
-- name    : TwoAgentSched.MaxMax.reduction_to_fmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:38.506115+00:00
-- url     : https://prove2.me/theorems/e2d4aa8c-7a98-481d-b4c3-95827b7099ef
-- title:
--   §4 — a minimizer of $f_{\max}$ with finite value solves $1\|f^A_{\max} : f^B_{\max}\le Q$; value $+\infty$ means infeasible
-- statement:
--   Consider $n_A\ge1$ A-jobs and $n_B$ B-jobs with nonnegative processing times and nondecreasing cost functions $f^A_h$, $f^B_k$, a bound $Q$, and the extended-real costs $f_i$ and objective $f_{\max}$ of the reduction of §4. Let $\sigma^*$ be a schedule that minimizes $f_{\max}$ over all schedules of the $n_A+n_B$ jobs (there are no precedence constraints).
--
--   1. If the minimum is a finite real number $f^*_{\max}$, then $\sigma^*$ is feasible and optimal for $1\|f^A_{\max} : f^B_{\max}\le Q$, and
--   $$f^A_{\max}(\sigma^*)=f^*_{\max}.$$
--   2. If the minimum is $+\infty$, then $1\|f^A_{\max} : f^B_{\max}\le Q$ has no feasible schedule.
--
--   This is the reduction through which the paper solves the two-agent problem with Lawler's algorithm for $1|prec|f_{\max}$.
--
--   **Formalization Note** "$1|prec|f_{\max}$" is taken with the empty precedence relation, the only one the two-agent problem has. "Finite objective function value" is stated as "the minimum equals a real number", which also excludes $-\infty$. Nonnegative processing times and monotone costs are the paper's standing assumptions of §3; they are kept as hypotheses.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 232, §4, the paragraph after the display of f_i(t) ("With these positions, …")

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Reduction

namespace TwoAgentSched.MaxMax

/-- §4, the reduction to `1|prec|f_max` (Agnetis et al. 2004, p. 232), with an empty precedence
relation. Let `σ*` be a schedule minimizing `f_max = max_i f_i(C_i)` (values in `[-∞, +∞]`) over
all schedules of the `nA + nB` jobs.
1. If the minimum is a finite value `f*`, then `σ*` is feasible and optimal for
   `1‖f^A_max : f^B_max ≤ Q`, and `f^A_max(σ*) = f*`.
2. If the minimum is `+∞`, then `1‖f^A_max : f^B_max ≤ Q` has no feasible schedule. -/
theorem reduction_to_fmax {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (hfA : ∀ h, Monotone (fA h))
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) (σ : List (Job nA nB))
    (hσ : MooreLateJobs.Shared.IsSchedule Finset.univ σ)
    (hmin : ∀ σ' : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ σ' →
      reducedMax p fA fB Q σ ≤ reducedMax p fA fB Q σ') :
    (∀ fstar : ℝ, reducedMax p fA fB Q σ = (fstar : EReal) →
      IsOptimal hA p fA fB Q σ ∧ maxCostA hA p fA σ = fstar) ∧
    (reducedMax p fA fB Q σ = ⊤ → ¬ ∃ l : List (Job nA nB), IsFeasible p fB Q l) := by sorry

end TwoAgentSched.MaxMax
