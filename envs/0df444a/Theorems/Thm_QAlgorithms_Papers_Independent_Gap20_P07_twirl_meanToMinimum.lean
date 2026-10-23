-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_twirl_meanToMinimum
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.twirl_meanToMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:25:52.701469+00:00
-- url     : https://prove2.me/theorems/c77e6a82-03f8-4531-bbc8-a8c72c430966
-- title:
--   Section 6.2 / (91)–(93): Haar twirling turns mean fidelity into minimum fidelity
-- statement:
--   Let $T$ be a CPTP endomorphism of a nonzero complex system of dimension $d$. With normalized Haar measure on the full unitary group, define
--   $$\widetilde T(X)=\int_{U(d)}U^*T(UXU^*)U\,dU.$$
--   This integral is a CPTP channel, and for every unit vector $\psi$,
--   $$\langle\psi|\widetilde T(|\psi\rangle\langle\psi|)|\psi\rangle=F_{\rm av}(T),\qquad F_{\min}(\widetilde T)=F_{\rm av}(T).$$
--   The integral averages whole logical-block unitaries. This computes the channel realized by the source's continuous forward-message construction and equates its minimum fidelity to the original mean.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 24, Section 6.2 / (91)–(93): Haar twirling turns mean fidelity into minimum fidelity

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

section HaarTwirlNorm

open scoped Matrix.Norms.L2Operator

/-- PDF pp.24--25, (91)--(93): computed whole-logical-block Haar integral,
constant pure-state survival overlap, and equality of the minimum and mean. -/
theorem twirl_meanToMinimum (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    IsChannel (QuditFidelity.haarTwirl d hd T) ∧
    (∀ X, QuditFidelity.haarTwirl d hd T X =
      ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
        conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ))
          (T (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)) ∂Schur.unitaryHaar d) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      effectProb (pureDensity psi) (QuditFidelity.haarTwirl d hd T (pureDensity psi)) =
        QuditFidelity.averageFidelity d hd T) ∧
    minimumFidelity d (QuditFidelity.haarTwirl d hd T) = QuditFidelity.averageFidelity d hd T := by sorry

end HaarTwirlNorm

end QAlgorithms.Papers.Independent.Gap20.P07

end
