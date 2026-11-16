-- Prove2me | Theorems.Thm_ParetoNCSched_Supplement_theorem_E_2
-- name    : ParetoNCSched.Supplement.theorem_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:45:27.00498+00:00
-- url     : https://prove2.me/theorems/480a5ab6-27ff-4fcc-8ec5-55a4504a70e2
-- title:
--   Theorem E.2 — every deterministic $R$-robust algorithm has consistency at least $c(R)$, with predicted orders or predicted sizes
-- statement:
--   Let $R>2$ and
--
--   $$c(R)=R\left(1-\left(1-\frac{R+2}{R^2}\right)^{\frac{R}{R+2}}\right).$$
--
--   Every deterministic algorithm $A$ for non-clairvoyant scheduling with predictions (minimizing the total completion time on one machine) with $\mathrm{rob}(A)\le R$ satisfies
--
--   $$\mathrm{cons}(A)\ge c(R),$$
--
--   both when $A$ receives a predicted order $\sigma$ and when it receives predicted sizes $y\in(0,\infty)^n$. Here a deterministic algorithm knows $n$ and the prediction, and at any time which jobs have completed and when; it assigns to every completion history a measurable rate function on the unfinished jobs. $\mathrm{cons}(A)$ and $\mathrm{rob}(A)$ are the suprema over all $n\ge1$ and all sizes $p\in(0,\infty)^n$ of $A(p,y)/\mathrm{OPT}(p)$, over correct, resp. all, predictions.
--
--   This is Theorem 1.2 of the paper. With Theorem 1.1 it shows that the Pareto-optimal consistency–robustness trade-off of deterministic algorithms is the curve $\{(c(R),R):R>2\}$, and that exact predicted sizes are worth no more than a predicted order.
--
--   **Formalization Note** Both clauses are stated, one per prediction model. The bound is on the supremum $\mathrm{cons}(A)$ (no single instance attains it). $c(R)$ is the base mission's `cR`.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm assigns to every completion history a measurable rate function on [C_k, ∞), supported on the jobs not in H → DetAlg: a rate function on all of ℝ for every list of (job, time) pairs, with IsSchedule and zero rates on the jobs of the list required everywhere; reason: values off [C_k, ∞) and at lists that are not histories are never used by the run; every rate function of the paper extends by 0, so the runs and costs are the same
--   - encoding: the run defined by induction over completions → algRate: n iterations of algStep (next completion = infimum of the times a remaining job reaches its size; simultaneous completions appended in index order; no further completion → the current rate function forever); reason: the paper's induction, written as an iteration; same run
--   - encoding: cons(A), rob(A) as suprema of A(p, y)/OPT(p) over n ≥ 1, p ∈ (0,∞)ⁿ → consOf/robOf in ℝ≥0∞, a job that never completes having C_j = ⊤, OPT the base infimum over all schedules; reason: OPT(p) ∈ (0,∞) for n ≥ 1 and p > 0, so the quotients are the paper's; an algorithm leaving a job unfinished has infinite cost, as in the paper
--   - encoding: jobs 1..n, predicted order σ, predicted sizes y ∈ (0,∞)ⁿ → jobs Fin n, σ : Equiv.Perm (Fin n) with the base IsCorrect, y : Fin n → ℝ with positivity required in the suprema; reason: Lean convention; same instances
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem E.2, p.32 (= Theorem 1.2, p.4); Appendix A, Model, p.15; Appendix E, Predicted sizes, p.31

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_algCost
import Definitions.Def_ParetoNCSched_Supplement_robOf
import Definitions.Def_ParetoNCSched_Supplement_consOf
import Definitions.Def_ParetoNCSched_Supplement_orderModel
import Definitions.Def_ParetoNCSched_Supplement_sizeModel
import Definitions.Def_ParetoNCSched_cR
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **Theorem E.2 (Lower bound)** (= Theorem 1.2, p.4). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix E.2, Theorem E.2, p.32:
"Let R > 2 and let c(R) be given by (1). Every deterministic algorithm A with rob(A) ≤ R satisfies
cons(A) ≥ c(R), whether it receives a predicted order or predicted sizes."

**Formalization Note.**
* Deterministic algorithms are those of Appendix A (`DetAlg`): maps from `(n, prediction,
  completion history)` to rate functions, with no access to the sizes; the run and its cost
  `A(p, y)` are `algRate`/`algCost`.
* `rob` and `cons` are the suprema over `n ≥ 1`, `p ∈ (0, ∞)ⁿ` and allowed (resp. correct)
  predictions of `A(p, y)/OPT(p)` in `ℝ≥0∞` (`robOf`, `consOf`); `OPT` is the base infimum over
  all schedules. The conclusion is a bound on the supremum, not on a single instance.
* One clause per prediction model: predicted orders (correct iff `IsCorrect p σ`) and predicted
  sizes (`y ∈ (0, ∞)ⁿ`, correct iff `y = p`). `c(R)` is the base `cR`. -/
theorem theorem_E_2 (R : ℝ) (hR : 2 < R) :
    (∀ A : DetAlg orderModel,
      robOf orderModel (fun _ p σ => algCost A p σ) ≤ ENNReal.ofReal R →
        ENNReal.ofReal (cR R) ≤ consOf orderModel (fun _ p σ => algCost A p σ)) ∧
    (∀ A : DetAlg sizeModel,
      robOf sizeModel (fun _ p y => algCost A p y) ≤ ENNReal.ofReal R →
        ENNReal.ofReal (cR R) ≤ consOf sizeModel (fun _ p y => algCost A p y)) := by sorry

end ParetoNCSched.Supplement
