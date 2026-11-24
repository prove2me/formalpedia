-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_Supplement_theorem_3_3
-- name    : SingleMachineSched.AlphaJSched.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:10:25.140831+00:00
-- url     : https://prove2.me/theorems/a0f222e7-2fae-462c-afe6-49fe60143a5c
-- title:
--   Theorem 3.3 — common alpha cost and simultaneous makespan bounds
-- statement:
--   Let the jobs have positive integral processing times, nonnegative integral releases and positive weights, indexed by nonincreasing weight-to-processing ratios. For each fixed $0<\alpha\le1$, let $C^\alpha_j$ be the completion times in the common-alpha schedule of the LP schedule. Then
--   $$\sum_jw_jC^\alpha_j\le\max\{1+1/\alpha,1+2\alpha\}\,Z_R,$$
--   $$\max\{1+1/(1/\sqrt2),1+2/\sqrt2\}=1+\sqrt2,$$
--   and, simultaneously,
--   $$\forall j,\quad C^\alpha_j\le(1+\alpha)C^*_{\max}.$$
--   The last inequality is equivalent to the makespan bound for the schedule, with the empty schedule assigned makespan zero. In particular the first inequality gives factor $1+\sqrt2$ at $\alpha=1/\sqrt2$. This provides a deterministic cost guarantee together with control of schedule length.
--
--   Differences from the source:
--   - encoding: jobs 1 through n, integral p_j > 0 and r_j >= 0 → Fin n jobs with natural-valued p and r and an explicit hp hypothesis; reason: zero-based labels change no instance; the empty instance has zero cost and makespan
--   - encoding: the standing indexing by nonincreasing w_j/p_j, ties by index → hsort with the published smallest-index LP schedule; reason: under the stated ordering this is exactly the paper priority rule
--   - encoding: alpha-points with 0 < alpha <= 1 → an explicit hα in (0,1] and the constant vector in alphaCompletion; reason: alpha-schedules are the published job-dependent construction specialized to a common parameter
--   - encoding: optimal nonpreemptive objective or makespan → infima over feasible real start times, with nonnegative makespan horizons; reason: the sets are nonempty and lower bounded and minima are attained among finitely many job orders, including the empty-instance convention
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 179 (PDF 15), Theorem 3.3

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_Optima

namespace SingleMachineSched.AlphaJSched.Supplement

/-- Theorem 3.3: common α, its special factor at 1/√2, and the simultaneous makespan bound. -/
theorem theorem_3_3 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1) :
    (∑ j, w j * (alphaCompletion p r (fun _ => α) j : ℝ) ≤
      max (1 + 1 / α) (1 + 2 * α) * Shared.zR p r w) ∧
    (max (1 + 1 / (1 / Real.sqrt 2)) (1 + 2 * (1 / Real.sqrt 2)) =
      1 + Real.sqrt 2) ∧
    (∀ j, (alphaCompletion p r (fun _ => α) j : ℝ) ≤
      (1 + α) * optMakespan p r) := by sorry

end SingleMachineSched.AlphaJSched.Supplement
