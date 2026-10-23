-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_partialTranspose_properties
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.partialTranspose_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:16:47.680145+00:00
-- url     : https://prove2.me/theorems/8f8985b6-8450-46fd-8b29-3924ec2e50f5
-- title:
--   Section 3.3 / (28): properties of the partial-transposition bound
-- statement:
--   For CPTP channels on nonzero complex Hilbert spaces, define $Q_\Theta(T)=\log_2\|T\Theta\|_{\rm cb}$, allowing $+\infty$. It has the following properties:
--   $$Q_\Theta(S\otimes T)=Q_\Theta(S)+Q_\Theta(T),\qquad Q_\Theta(S\circ T)\le\min\{Q_\Theta(S),Q_\Theta(T)\}.$$
--   The second formula requires composability. For every integer $d\ge1$,
--   $$Q_\Theta(\mathrm{id}_d)=Q(\mathrm{id}_d)=\log_2d.$$
--   Also $Q_\Theta(T)=0$ whenever $T\Theta$ is completely positive; it is then CPTP because $T$ is trace preserving. In particular the bound vanishes if every reference extension of $T$ has positive-partial-transpose output on every input state. In both vanishing cases $Q(T)=0$ as well. These give all stated capacity-like properties and the PPT consequence.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 11, Section 3.3 / (28): properties of the partial-transposition bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF p.11, (28): all four capacity-like properties, and the PPT consequence.
PPT is expressed for all reference systems by normalized positive partial transposes. -/
theorem partialTranspose_properties :
    (∀ {I J K L : Type} [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
      (S : Operation I J) (T : Operation K L),
      IsTraceClassChannel S → IsTraceClassChannel T →
      transposeBound (traceClassTensorMap S T) = transposeBound S + transposeBound T) ∧
    (∀ {I J K : Type} [Nonempty I] [Nonempty J] [Nonempty K]
      (S : Operation J K) (T : Operation I J),
      IsTraceClassChannel S → IsTraceClassChannel T →
      transposeBound (S ∘ T) ≤ min (transposeBound S) (transposeBound T)) ∧
    (∀ d : ℕ, 0 < d → transposeBound (id : Operation (Fin d) (Fin d)) =
      qubitReferenceCapacity (id : Operation (Fin d) (Fin d)) ∧
      qubitReferenceCapacity (id : Operation (Fin d) (Fin d)) = ENNReal.ofReal (Real.logb 2 d)) ∧
    (∀ {I J : Type} [Nonempty I] [Nonempty J] (T : Operation I J),
      IsTraceClassChannel T → IsTraceClassChannel (T ∘ transpose) →
        transposeBound T = 0 ∧ qubitReferenceCapacity T = 0) ∧
    (∀ {I J : Type} [Nonempty I] [Nonempty J] (T : Operation I J),
      IsTraceClassChannel T →
      (∀ (A : Type) (rho : State (I × A)),
        QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity
          (tensorApply transpose (tensorApply T rho.coefficients))) →
        transposeBound T = 0 ∧ qubitReferenceCapacity T = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
