-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_Supplement_theorem_6_1_counterexample
-- name    : RiskAverseSDDP.Subdiff.Supplement.theorem_6_1_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:36:27.192574+00:00
-- url     : https://prove2.me/theorems/a5127e93-af26-4d33-b36a-ea79c95a885d
-- title:
--   Theorem 6.1 (corrected: refutation of the printed sampling test)
-- statement:
--   The explicit sampling test printed in Theorem 6.1 (p. 20) does not imply the convergence claimed there. On the probability space of a fair bit, use the three-stage zero-cost singleton-decision instance described in `Algorithm3Counterexample`. Draw the bit once and repeat its scenario forever. Every sample is measurable and has the correct marginal law; (H2) holds with $\varepsilon=1$.
--
--   Writing $y^k_n$ for the indicator that node $n$ is selected at iteration $k$, the random variables printed in the theorem satisfy
--   $$y^k_{n^k_T}=1$$
--   for every iteration and every outcome. They are therefore independent. Whole scenarios are correlated across iterations. The full `TreeModel.IsRun3` predicate holds for the explicit `zeroTreeModel`, `zeroTreeRules` and `zeroTreeRun`, as do the reduced scalar recurrences. True model values and failure of the actual model limits are asserted directly; the claim is not only about an unrelated scalar recurrence. For every outcome, the other second-stage node retains approximation $-\infty$, whereas its true value is zero. Hence conclusion (i) fails. The approximate first-stage values also remain $-\infty$, whereas the true optimum is zero, so the value-convergence part of (ii) fails. The decisions are all zero, so their optimality does not fail.
--
--   **Formalization Note** This item refutes the displayed indicator test, even granting the usual correct marginal meaning of sampling. If the introductory prose is instead read as an independent requirement that whole scenarios are independent, this process is excluded; the item does not refute that stronger reading. No new sampling assumption is silently added to Theorem 6.1. The startup interpretation is the extended-real convention of (6.45), consistent with the printed $-\infty$ initialization. See `DISPROOF.md` for the source anchors and the exact domain of the refutation.
--
--   Differences from the source:
--   - correction: Theorem 6.1 asserts convergence under independence of the selected-leaf indicators y^k_(n^k_T) → an explicit run satisfies that printed test and the correct marginal scenario laws, but both value convergence conclusions fail; reason: each selected-leaf indicator is identically one; repeated fair scenarios pass that test and leave an unvisited node at minus infinity
--   - reading: the prose says the samples are independent, followed by a colon and an explicit indicator test → the refutation applies to the explicit indicator test, not to the stronger interpretation that whole scenario samples are independent; reason: the printed indicator sequence is constant; imposing independence of whole scenarios would exclude the exhibited process
--   - encoding: Algorithm 3 uses value functions and their subgradients on decision histories → all feasible decisions are zero and all cut slopes are zero, so constant functions are recorded by their scalar values; reason: the singleton feasible sets and zero costs make (6.45), (6.47), (6.49) reduce exactly to the stated recurrences
--   - correction: initial approximations are minus infinity while finite epigraph minimizers need not exist → feasible decisions minimize the extended-real startup objective; reason: Algorithm 3 explicitly solves the value-function problem (6.45); this boundary convention agrees with its initialization
-- source:
--   Guigues, arXiv:1408.4439v4, p. 20, Theorem 6.1; Algorithm 3, pp. 19–20

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm3Counterexample
open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

/-- Refutation of the explicit independence test printed in Theorem 6.1, p. 20.
The selected-leaf indicators are independent constants, although the sampled scenarios
are repeated forever. Both the unvisited-node convergence and first-stage value
convergence fail, for every outcome. -/
theorem theorem_6_1_counterexample :
    zeroData.H2 1 ∧
    zeroTreeModel.H2 1 ∧ zeroTreeModel.Standing ∧
    IsProbabilityMeasure zeroLaw ∧
    (∀ k, Measurable (repeatedSample k)) ∧
    (∀ k (b : Bool), zeroLaw {ω | repeatedSample (k + 1) ω = b} = (1 / 2 : ℝ≥0∞)) ∧
    (∀ k ω, zeroProcess (repeatedSample k ω) = zeroProcess ω) ∧
    (∀ k ω, zeroSelected k ω (.leaf (repeatedSample k ω)) = 1) ∧
    iIndepFun (fun k : ℕ => fun ω : Bool => zeroSelected (k + 1) ω (.leaf (repeatedSample (k + 1) ω))) zeroLaw ∧
    (¬ iIndepFun (fun k : ℕ => repeatedSample (k + 1)) zeroLaw) ∧
    (∀ ω, IsZeroAlgorithm3Run (fun k => repeatedSample k ω) (zeroApprox ω)) ∧
    (∀ ω, zeroTreeModel.IsRun3 zeroTreeRules (fun _ => zeroPath ω) (zeroTreeRun ω)) ∧
    (∀ s, s < 3 → ∀ ν : ZeroLevel s, ∀ z, zeroTreeModel.Q s ν z = 0) ∧
    (zeroTreeModel.Q1 = 0) ∧
    (∀ ω,
      ¬ Tendsto (fun k => (zeroTreeRun ω).Qm k 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω)) -
          zeroTreeModel.Q 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω))) atTop (𝓝 0) ∧
      ¬ Tendsto (fun k => zeroTreeModel.stageVal 0 zeroTreeModel.first
          ((zeroTreeRun ω).Qm k 0 zeroTreeModel.first) (Hist.empty 1)) atTop (𝓝 zeroTreeModel.Q1)) ∧
    (∀ ω, (∀ k, zeroApprox ω k (.middle (!ω)) = ⊥) ∧
      ¬ Tendsto (fun k => zeroApprox ω k (.middle (!ω)) - zeroTrueValue (.middle (!ω))) atTop (𝓝 0) ∧
      ¬ Tendsto (fun k => zeroApprox ω k .first) atTop (𝓝 (zeroTrueValue .first))) := by sorry

end RiskAverseSDDP.Subdiff.Supplement
