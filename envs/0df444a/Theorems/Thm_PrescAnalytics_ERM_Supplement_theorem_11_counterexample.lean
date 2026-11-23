-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_Supplement_theorem_11_counterexample
-- name    : PrescAnalytics.ERM.Supplement.theorem_11_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:01:06.229432+00:00
-- url     : https://prove2.me/theorems/26df2d05-4bc8-4436-8d4f-bb97711e14dd
-- title:
--   Theorem 11 (companion theorem; not used in the proof of the goal) — corrected: counterexample to censoring claim
-- statement:
--   The printed censoring theorem is false under marginal no-shared-atoms as stated. For the explicit law $X=T$, $Y=T+B$, $V=T+2D$, with $T$ uniform on $[0,1/4]$ and independent fair bits $B,D$, there exists an iid observation process satisfying every printed censoring premise and every corresponding premise for all five weighting methods (including all three kernels). The feasible decisions are $0$ and $1$, and the cost is the bounded, jointly $C^2$ function specified by the accompanying definition. With $C=1$ and $\delta=1/4$, each transformed prescription fails both claimed properties:
--   $$\forall m,\qquad\neg\operatorname{AsymptoticallyOptimal}(\widehat{\mathcal Z}^{\mathrm{KM},m})\quad\text{and}\quad\neg\operatorname{Consistent}(\widehat{\mathcal Z}^{\mathrm{KM},m}).$$
--   The full-information optimizer is $0$ almost everywhere. Conditional upper-support ordering and the entire domain of each method are retained in the counterexample. The construction identifies a substantive obstruction to the claimed extension, rather than a proof gap alone.
--
--   **Formalization Note** The printed statement assumes only no shared marginal atoms; this does not exclude conditional ties, so the Lean states an explicit counterexample instead of adding an unprinted premise. The theorem is a draft target with an unproved Lean body; the mathematical counterexample and its population-limit calculation are documented in DISPROOF.md.
--
--   Differences from the source:
--   - correction: Under the listed censoring assumptions all five methods are optimal and consistent. → An explicit iid law and smooth bounded cost meet those assumptions but all five methods fail both conclusions.; reason: At each x the strict indicator misclassifies conditional ties. The low-response event hazard has mass 1/4 over a risk starting at 1 and ending at 1/4, producing residual high mass 4^(-1/3) rather than 1/2; see DISPROOF.md and source pp. 24–25, 51.
--   - encoding: Y is scalar and observations are indexed from 1. → Scalar responses use the published one-dimensional Euclidean carrier, observations start at 0, ties in U use lower original index, zero ratios are totalized as zero.; reason: These conventions preserve (24) and do not renormalize away residual product-limit mass.
--   - reading: Conditional upper endpoints and conditional independence are written in ordinary probability notation. → Upper endpoints are EReal essential suprema under the fixed conditional kernel, with a full-measure covariate domain Xs; independence is a kernel rectangle factorization.; reason: Conditional laws are only determined almost everywhere. The witness Xs selects their valid versions without imposing atomlessness conditionally.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 25, Theorem 11

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_CensorExample

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Counterexample to Theorem 11 as printed (pp. 24–25, proof p. 51).
All five methods, including all three kernels where applicable, fail under the printed assumptions.
The replacement is an explicit refutation, not a silently strengthened consistency claim. -/
theorem theorem_11_counterexample :
    ∃ (hν : IsProbabilityMeasure censorExampleLaw)
      (hμ : IsProbabilityMeasure examplePairLaw)
      (P : Measure (ℕ → EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × ℝ)))
      (hP : IsProbabilityMeasure P),
    letI := hν
    letI := hμ
    letI := hP
    let S := fun i (ω : ℕ → EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × ℝ)) => ω i
    ∃ Xs : Set (EuclideanSpace ℝ (Fin 1)),
      (∀ i, Measurable (S i)) ∧ iIndepFun S P ∧
      (∀ i, P.map (S i) = censorExampleLaw) ∧
      (∀ᵐ p ∂censorExampleLaw, p.1 ∈ Xs) ∧
      CensorAssumptions censorExampleLaw Xs ∧
      censorExampleLaw {p | p.2.1 0 = p.2.2} = (1/4 : ℝ≥0∞) ∧
      PrescAnalytics.KNN.Assumption3 examplePairLaw exampleCost exampleDecisions ∧
      PrescAnalytics.KNN.Assumption4 exampleCost exampleDecisions Set.univ ∧
      PrescAnalytics.KNN.Assumption5 examplePairLaw exampleCost exampleDecisions Xs Set.univ ∧
      (∀ z ∈ exampleDecisions, Integrable
        (fun p => |exampleCost z p.2| * max (Real.log |exampleCost z p.2|) 0) examplePairLaw) ∧
      (∃ f : EuclideanSpace ℝ (Fin 1) → ℝ,
        Measurable f ∧ (∀ x, 0 ≤ f x) ∧
        examplePairLaw.map Prod.fst = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ContDiffOn ℝ 2 f (examplePairLaw.map Prod.fst).support ∧
        ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ (examplePairLaw.map Prod.fst).support, a ≤ f x ∧ f x ≤ b) ∧
      ((∀ z ∈ exampleDecisions, ∃ g : ℝ, ∀ y : EuclideanSpace ℝ (Fin 1), |exampleCost z y| ≤ g) ∧
        ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
          exampleCost p.1 p.2)) ∧
      (∀ᵐ x ∂(examplePairLaw.map Prod.fst),
        PrescAnalytics.KNN.optSet examplePairLaw exampleCost exampleDecisions x = {scalarVector 0}) ∧
      (∀ m : Method,
        ¬ PrescAnalytics.KNN.IsAsymptoticallyOptimal P examplePairLaw exampleCost exampleDecisions
          (censoredPrescription m 1 (1/4) exampleCost exampleDecisions S) ∧
        ¬ PrescAnalytics.KNN.IsConsistent P examplePairLaw exampleCost exampleDecisions
          (censoredPrescription m 1 (1/4) exampleCost exampleDecisions S)) := by sorry

end PrescAnalytics.ERM.Supplement
