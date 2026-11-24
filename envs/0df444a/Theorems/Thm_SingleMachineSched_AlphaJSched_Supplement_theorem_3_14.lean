-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_Supplement_theorem_3_14
-- name    : SingleMachineSched.AlphaJSched.Supplement.theorem_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:11:49.0396+00:00
-- url     : https://prove2.me/theorems/4e01f134-2848-4265-bc5d-f0f1c35b5b61
-- title:
--   Theorem 3.14 — on-line deterministic and randomized competitive ratios
-- statement:
--   Let the jobs have positive integral processing times, nonnegative integral releases and positive weights indexed by nonincreasing weight-to-processing ratios. Let $\operatorname{OPT}$ be the minimum weighted completion cost over all feasible off-line nonpreemptive schedules with real start times. Write $C^{\mathrm{on}}_j(\boldsymbol\alpha)$ for the on-line alpha-point schedule, which waits for each job's alpha-point before starting it.
--
--   (a) With the common choice $\alpha=1/\sqrt2$,
--   $$1+\sqrt2\le2.4143,\qquad \sum_jw_jC^{\mathrm{on}}_j(\alpha)\le(1+\sqrt2)\operatorname{OPT}.$$
--   (b) Let $0<\gamma<1$ satisfy
--   $$\gamma+\log(2-\gamma)=e^{-\gamma}((2-\gamma)e^\gamma-1).$$
--   Using the published constants $\delta=\gamma+\log(2-\gamma)$, $c=1+e^{-\gamma}/\delta$ and density $g(a)=(c-1)e^a$ on $(0,\delta]$ (zero elsewhere), every pairwise independent draw with coordinate law $g$ gives integrable total cost and
--   $$c<1.6853,\qquad \mathbb E\!\left[\sum_jw_jC^{\mathrm{on}}_j(\boldsymbol\alpha)\right]\le c\operatorname{OPT}.$$
--   For every valid parameter vector, the construction is on-line: if a second sorted instance, with any number $m$ of jobs, has exactly the same jobs released by time $t$ (matched by a relabelling $e$ that preserves their relative priority order), with the same processing times, releases, weights and parameters, then each job released by $t$ has started by $t$ in the first instance exactly when its image has in the second, at the same start time. The number and data of the jobs released after $t$, and their positions in the priority order, may differ. These conclusions give the two competitive guarantees against the off-line optimum.
--
--   **Formalization Note** Start times are real completion times minus processing times. The two running-time assertions $O(n\log n)$ are outside the authorized formalization scope and are not stated. Nonanticipativity is a conclusion, not an assumption about the schedule.
--
--   Differences from the source:
--   - encoding: jobs 1 through n, integral p_j > 0 and r_j >= 0 → Fin n jobs with natural-valued p and r and an explicit hp hypothesis; reason: zero-based labels change no instance; the empty instance has zero cost and makespan
--   - encoding: the standing indexing by nonincreasing w_j/p_j, ties by index → hsort with the published smallest-index LP schedule; reason: under the stated ordering this is exactly the paper priority rule
--   - encoding: optimal nonpreemptive objective or makespan → infima over feasible real start times, with nonnegative makespan horizons; reason: the sets are nonempty and lower bounded and minima are attained among finitely many job orders, including the empty-instance convention
--   - encoding: finite expected cost under pairwise independent random alpha_j → Integrable together with the Bochner integral inequality for every probability measure with the specified marginals and pairwise IndepFun; reason: this excludes total-integral defaults and retains pairwise rather than full independence
--   - encoding: construct the schedule on-line from jobs known by t → equality of started-job sets and their starts for any second sorted instance, of any size m, whose jobs released by t correspond to the first instance's by a priority-order-preserving relabelling e with identical data; reason: a nonpreemptive history is determined by these starts and the processing times revealed at release
--   - generalization: Theorem 3.14(b) quotes the rounded competitive ratio 1.6853 → the exact bound c times OPT together with c < 1.6853; reason: the proof on p. 189 transfers the preceding analysis, with the exact c of Theorem 3.9; OPT is nonnegative, so this implies the printed rounded bound
--   - encoding: the two O(n log n) running-time assertions → no running-time assertion; reason: the supplement brief explicitly excludes these computational complexity clauses; all planned performance and on-line clauses are retained
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 189 (PDF 25), Theorem 3.14

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_OnlineSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_Optima
import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG

namespace SingleMachineSched.AlphaJSched.Supplement

open MeasureTheory ProbabilityTheory

/-- Theorem 3.14: deterministic and randomized competitive bounds against OPT,
plus the on-line property for every valid vector of α_j: the schedule up to time t
is the same in every instance (of any size) whose jobs released by t are the same, in the
same relative priority order. Running time is not encoded. -/
theorem theorem_3_14 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    (1 + Real.sqrt 2 ≤ (2.4143 : ℝ) ∧
      ∑ j, w j * onlineCompletion p r (fun _ => 1 / Real.sqrt 2) j ≤
        (1 + Real.sqrt 2) * optValue p r w) ∧
    (∀ γ : ℝ, (0 < γ ∧ γ < 1 ∧
        γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) →
      cConst γ < 1.6853 ∧
        ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
          (∀ j, μ.map (fun a => a j) = gMeasure γ) →
          (∀ j k, j ≠ k → IndepFun (fun a => a j) (fun a => a k) μ) →
          Integrable (fun a => ∑ j, w j * onlineCompletion p r a j) μ ∧
            ∫ a, ∑ j, w j * onlineCompletion p r a j ∂μ ≤
              cConst γ * optValue p r w) ∧
    (∀ (m : ℕ) (p' r' : Fin m → ℕ) (w' : Fin m → ℝ) (α : Fin n → ℝ) (α' : Fin m → ℝ),
      (∀ j, 0 < p' j) → (∀ j, 0 < w' j) →
      (∀ j k : Fin m, j ≤ k → w' k / p' k ≤ w' j / p' j) →
      (∀ j, 0 < α j ∧ α j ≤ 1) → (∀ j, 0 < α' j ∧ α' j ≤ 1) →
      ∀ (t : ℝ) (e : Fin n → Fin m),
        (∀ j k, (r j : ℝ) ≤ t → (r k : ℝ) ≤ t → (j < k ↔ e j < e k)) →
        (∀ k', (r' k' : ℝ) ≤ t → ∃ j, (r j : ℝ) ≤ t ∧ e j = k') →
        (∀ j, (r j : ℝ) ≤ t →
          p' (e j) = p j ∧ r' (e j) = r j ∧ w' (e j) = w j ∧ α' (e j) = α j) →
        ∀ j, (r j : ℝ) ≤ t →
          ((onlineCompletion p r α j - (p j : ℝ) ≤ t ↔
            onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ) ≤ t) ∧
          (onlineCompletion p r α j - (p j : ℝ) ≤ t →
            onlineCompletion p r α j - (p j : ℝ) =
              onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ)))) := by sorry

end SingleMachineSched.AlphaJSched.Supplement
