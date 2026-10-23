-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_pureState_traceDistance
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.pureState_traceDistance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:18:01.059409+00:00
-- url     : https://prove2.me/theorems/9ca9c1eb-b7ce-4c6c-ae71-5961b0e4463c
-- title:
--   Lemma 4.1 / (31): pure-state trace distance and equality cases
-- statement:
--   Let $\rho$ be a positive trace-class operator of trace one on an arbitrary nonzero complex Hilbert space, and let $\psi$ have norm one. Then
--   $$\|\rho-|\psi\rangle\langle\psi|\|_1\le2\sqrt{1-\langle\psi|\rho|\psi\rangle}.$$
--   Equality holds if and only if $\rho$ is pure or $\psi$ is orthogonal to its support, equivalently its expectation of $\rho$ is zero. This retains the equality characterization used in the proof. The printed word “strict” is corrected to “equality”: the identical-pure-state case gives $0=0$. The bound compares an arbitrary density state with a pure reference.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 12, Lemma 4.1 / (31): pure-state trace distance and equality cases

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

/-- PDF p.12, Lemma 4.1, (31). Printed: 'strict iff'. Changed to equality iff,
as the proof explicitly computes and characterizes equality. At rho=|psi><psi|
both sides are zero. No finite-dimensional restriction is imposed. For a positive
rho, zero expectation is equivalent to orthogonality to its support. -/
theorem pureState_traceDistance {I : Type} [Nonempty I]
    (rho : State I) (psi : Hilbert I) (hpsi : ‖psi‖ = 1) :
    let overlap := (tracePair rho.coefficients (rankOne psi)).re
    traceSize (rho.coefficients - rankOne psi) ≤ ENNReal.ofReal (2 * Real.sqrt (1 - overlap)) ∧
    (traceSize (rho.coefficients - rankOne psi) = ENNReal.ofReal (2 * Real.sqrt (1 - overlap)) ↔
      (∃ phi : Hilbert I, ‖phi‖ = 1 ∧ rho.coefficients = rankOne phi) ∨ overlap = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
