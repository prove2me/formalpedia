-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_fidelity_controlsOrdinaryNorm
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.fidelity_controlsOrdinaryNorm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:18:49.74237+00:00
-- url     : https://prove2.me/theorems/fa774f5d-8fe2-48de-93fe-3b3bd09369fe
-- title:
--   Lemma 4.2 / (37): fidelity controls ordinary channel norm
-- statement:
--   Let $T$ be a CPTP endomorphism of a nonzero finite-dimensional complex system. In the Schroedinger convention let $\|\cdot\|_{1\to1}$ be the induced trace norm on all complex matrices. Then
--   $$\|T-\mathrm{id}\|_{1\to1}\le4\sup_{\|\psi\|=1}\sqrt{1-\langle\psi|T(|\psi\rangle\langle\psi|)|\psi\rangle}.$$
--   The map norm is equivalently the operator norm of the Heisenberg adjoint. This bound uses normalized pure states and a constant independent of dimension.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 13, Lemma 4.2 / (37): fidelity controls ordinary channel norm

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

/-- PDF p.13, Lemma 4.2, (37): ordinary map norm is the induced trace norm
in this Schroedinger convention; every vector in the supremum has norm one. -/
theorem fidelity_controlsOrdinaryNorm (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    ordinaryNorm d (fun X => T X - X) ≤ 4 * sSup {r : ℝ |
      ∃ psi : EuclideanSpace ℂ (Fin d), IsState psi ∧
        r = Real.sqrt (1 - effectProb (pureDensity psi) (T (pureDensity psi)))} := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
