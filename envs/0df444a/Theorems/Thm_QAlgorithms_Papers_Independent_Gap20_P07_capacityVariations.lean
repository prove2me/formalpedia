-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_capacityVariations
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.capacityVariations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:00:35.664155+00:00
-- url     : https://prove2.me/theorems/e2450003-29fd-496a-bd1d-47d3cefe90cf
-- title:
--   Abstract and Sections 2–7: equivalent quantum capacity definitions
-- statement:
--   Let $T$ be a CPTP channel between nonzero complex Hilbert spaces, with independent memoryless uses, arbitrary CPTP coding, and no initial shared entanglement. Let $Q(T)$ be the supremum of positive rates in Definition 2.1, measured in qubits per use, using the full completely bounded trace norm. Then
--   $$Q(T)=Q_{\min}(T)=Q_{e,\min}(T)=Q_{\rm av}(T)=Q_c(T)=Q_{1\to1}(T)=Q_{\rm spor}(T)=Q_{\exp}(T)=Q_{\rm QAEP}(T)=Q_{\rm expdim}(T)=Q_{\rm gen}(T)=Q_{\rm iso}(T)=Q_{\rm cf}(T).$$
--   The terms denote, respectively, minimum pure-state fidelity, worst-case entanglement fidelity, Haar average fidelity, maximally mixed source fidelity, ordinary induced trace-norm error, sporadic block lengths, some positive exponential error exponent, QAEP entropy sources, exponentially bounded source dimensions with a source-dependent growth constant, entanglement generation from arbitrary normalized inputs, isometric encoding, and unrestricted finite forward messages per block. Each is an extended nonnegative supremum. Also $Q(T\otimes S)=Q(T)$ for every operational measurement-and-preparation channel $S$; every positive $R<Q(T)$ admits all-block codes with error at most $C e^{-an}$ for some $C,a>0$; and
--   $$\lim_{\epsilon\downarrow0}Q_\epsilon(T)=Q(T).$$
--   Here $Q_\epsilon$ uses eventual full-cb error at most $\epsilon$. These are equalities of capacities, without asserting endpoint achievability. Zero-error and unconstrained entropy capacities are exceptions. This result identifies the qualified equivalence asserted in the abstract.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 1, Abstract and Sections 2–7: equivalent quantum capacity definitions

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

/-- PDF p.1 and Sections 2--7: the qualified abstract claim, excluding the
rejected exact-zero-error and unconstrained entropy variants. The capacities,
not endpoint sets of achievable rates, coincide. -/
theorem capacityVariations {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    (∀ c : FidelityCriterion, fidelityCapacity T c = qubitReferenceCapacity T) ∧
    sporadicCapacity T = qubitReferenceCapacity T ∧
    ordinaryCapacity T = qubitReferenceCapacity T ∧
    exponentialCapacity T = qubitReferenceCapacity T ∧
    sourceEntropyCapacity T QuantumSource.QAEP = qubitReferenceCapacity T ∧
    sourceEntropyCapacity T QuantumSource.ExponentialDimension = qubitReferenceCapacity T ∧
    variableSourceGenerationCapacity T = qubitReferenceCapacity T ∧
    isometricCapacity T = qubitReferenceCapacity T ∧
    instrumentForwardCapacity T (fun _ _ => True) = qubitReferenceCapacity T ∧
    (∀ {K L : Type} [Nonempty K] [Nonempty L] (S : Operation K L),
      IsTraceClassChannel S → MeasurePrepare S →
        qubitReferenceCapacity (traceClassTensorMap T S) = qubitReferenceCapacity T) ∧
    (∀ R : ℝ, 0 < R → ENNReal.ofReal R < qubitReferenceCapacity T → ExponentialReliable T R) ∧
    Tendsto (finiteErrorCapacity T) (𝓝[>] (0 : ℝ)) (𝓝 (qubitReferenceCapacity T)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
