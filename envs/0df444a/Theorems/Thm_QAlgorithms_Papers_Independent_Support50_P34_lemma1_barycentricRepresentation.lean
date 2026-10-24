-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma1_barycentricRepresentation
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma1_barycentricRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:36:26.739775+00:00
-- url     : https://prove2.me/theorems/5b23b706-020a-48bd-a382-360cf2a4fa58
-- title:
--   Lemma 1: barycentric representation of the closed convex hull
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $A$ a trace-norm closed subset of its density operators $S(\mathcal H)$. Every state $\rho$ in the trace-norm closed convex hull of $A$ is the barycenter of a Borel probability measure supported on $A$:
--
--   $$\rho\in\overline{\operatorname{co}}(A)\quad\Longrightarrow\quad\exists\mu\in\mathcal P(A),\quad b(\mu)=\rho.$$
--
--   Here $b(\mu)=\int_A\sigma\,\mu(d\sigma)$ is the trace-norm Bochner integral. This gives the representation underlying the extremal extensions below.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 5, Lemma 1: barycentric representation of the closed convex hull

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

/-- Lemma 1, arXiv:0904.1963v3, PDF p.5: closed convex hull barycentric representation. -/
theorem lemma1_barycentricRepresentation (b : HilbertBasis I ℂ H)
    (A : Set (QuantumState b)) (hA : IsClosed A) (rho : QuantumState b)
    (hrho : rho ∈ stateClosedHull b A) :
    ∃ mu : ProbabilityMeasure A, mu ∈ stateFiber b A rho := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
