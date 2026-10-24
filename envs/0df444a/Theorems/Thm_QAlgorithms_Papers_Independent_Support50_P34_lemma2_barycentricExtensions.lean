-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma2_barycentricExtensions
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma2_barycentricExtensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:37:18.493093+00:00
-- url     : https://prove2.me/theorems/a37fc43f-bf74-4c05-a3ae-fadcc060d2ca
-- title:
--   Lemma 2 (A–B): semicontinuity of barycentric extremal extensions
-- statement:
--   Let $A\subseteq S(\mathcal H)$ be trace-norm closed and let $f:A\to[-\infty,+\infty]$ be lower semicontinuous with a finite real lower bound. Write $\mathcal P_\rho(A)$ for Borel probabilities with barycenter $\rho$, and define
--
--   $$\check f_A(\rho)=\inf_{\mu\in\mathcal P_\rho(A)}\int_A f\,d\mu,\qquad \hat f_A(\rho)=\sup_{\mu\in\mathcal P_\rho(A)}\int_A f\,d\mu.$$
--
--   On $\overline{\operatorname{co}}(A)$, the function $\check f_A$ is convex and lower semicontinuous, and its infimum is attained at every state. If the barycenter map into this closed convex hull is open in its relative topology, then $\hat f_A$ is concave and lower semicontinuous there. This distinguishes the two extremal extensions and the one attainment assertion.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 5, Lemma 2 (A–B): semicontinuity of barycentric extremal extensions

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*}

section Statements

variable [hsep : TopologicalSpace.SeparableSpace H] [hI : Countable I]

include hsep hI

/-- Lemma 2 A–B, arXiv:0904.1963v3, PDF pp.5–6: both extremal extensions,
with attainment for the lower extension only. -/
theorem lemma2_barycentricExtensions (b : HilbertBasis I ℂ H)
    (A : Set (QuantumState b)) (hA : IsClosed A) (f : A → EReal)
    (hf : LowerSemicontinuous f) (hb : LowerBounded f) :
    (StateConvexOn b (stateClosedHull b A) (lowerRoof b A f) ∧
      LowerSemicontinuous (fun rho : stateClosedHull b A => lowerRoof b A f rho.val) ∧
      ∀ rho ∈ stateClosedHull b A, ∃ mu ∈ stateFiber b A rho,
        lowerRoof b A f rho = extendedIntegral (mu : Measure A) f) ∧
    (BarycenterOpenIntoHull b A →
      StateConcaveOn b (stateClosedHull b A) (upperRoof b A f) ∧
      LowerSemicontinuous (fun rho : stateClosedHull b A => upperRoof b A f rho.val)) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
