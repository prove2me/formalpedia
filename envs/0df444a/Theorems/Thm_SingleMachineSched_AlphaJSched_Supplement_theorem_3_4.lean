-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_Supplement_theorem_3_4
-- name    : SingleMachineSched.AlphaJSched.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:11:04.778365+00:00
-- url     : https://prove2.me/theorems/ef98f9d8-21cb-4e0b-9840-a3ea68078977
-- title:
--   Theorem 3.4 — uniform pairwise independent alpha-points give factor two
-- statement:
--   Let the jobs have positive integral processing times, nonnegative integral releases and positive weights in nonincreasing weight-to-processing ratio order. Draw the parameters $\alpha_j$ pairwise independently, each uniformly on $(0,1]$. If $C_j^{\boldsymbol\alpha}$ is the completion time in the resulting published job-dependent alpha-point schedule, then its total weighted completion time is integrable and
--   $$\mathbb E\!\left[\sum_jw_jC_j^{\boldsymbol\alpha}\right]\le2Z_R.$$
--   The comparison is with the optimal relaxation value $Z_R=Z_D$, not the cost of an arbitrary preemptive schedule. This is the uniform-density companion to the goal's truncated exponential guarantee.
--
--   Differences from the source:
--   - encoding: jobs 1 through n, integral p_j > 0 and r_j >= 0 → Fin n jobs with natural-valued p and r and an explicit hp hypothesis; reason: zero-based labels change no instance; the empty instance has zero cost and makespan
--   - encoding: the standing indexing by nonincreasing w_j/p_j, ties by index → hsort with the published smallest-index LP schedule; reason: under the stated ordering this is exactly the paper priority rule
--   - encoding: finite expected cost under pairwise independent random alpha_j → Integrable together with the Bochner integral inequality for every probability measure with the specified marginals and pairwise IndepFun; reason: this excludes total-integral defaults and retains pairwise rather than full independence
--   - encoding: uniform distribution on (0,1] → every coordinate marginal equals volume.restrict (Set.Ioc 0 1); reason: the interval has Lebesgue measure one, so this is the stated probability law
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 181 (PDF 17), Theorem 3.4

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.AlphaJSched.Supplement

open MeasureTheory ProbabilityTheory

/-- Theorem 3.4: pairwise independent uniform α_j give expected cost at most 2 Z_R. -/
theorem theorem_3_4 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
      (∀ j, μ.map (fun a => a j) = volume.restrict (Set.Ioc 0 1)) →
      (∀ j k, j ≠ k → IndepFun (fun a => a j) (fun a => a k) μ) →
      Integrable (fun a => ∑ j, w j * (alphaCompletion p r a j : ℝ)) μ ∧
        ∫ a, ∑ j, w j * (alphaCompletion p r a j : ℝ) ∂μ ≤
          2 * Shared.zR p r w := by sorry

end SingleMachineSched.AlphaJSched.Supplement
