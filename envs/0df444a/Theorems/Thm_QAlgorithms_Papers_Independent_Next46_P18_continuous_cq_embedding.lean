-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_continuous_cq_embedding
-- name    : QAlgorithms.Papers.Independent.Next46.P18.continuous_cq_embedding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:09:42.021058+00:00
-- url     : https://prove2.me/theorems/e067e26e-3930-4c50-8749-f6c0d6a92ebf
-- title:
--   §3, unnumbered continuous c-q embedding
-- statement:
--   Let $(X,\mu)$ be a sigma-finite signal measure space with nonzero separable $L^2(X,\mu)$, and let $x\mapsto\rho_x$ be a trace-norm measurable field of normalized positive trace-class operators on a nonzero separable output Hilbert space. Identify the input Hilbert space with $L^2(X,\mu)$ using a unitary $V$. There exist the position multiplication PVM $M$, normal-state probability laws $\mu_\rho(S)=\operatorname{Tr}(\rho M(S))$, and a normal completely positive trace-preserving channel $\Phi$ such that
--
--   $$\Phi(\rho)=\int_X\rho_x\,\mu_\rho(dx),\qquad V\Phi^*(B)V^*=M_{x\mapsto\operatorname{Tr}(\rho_xB)}.$$
--
--   The notation $M_f$ denotes multiplication by the bounded scalar function $f$. The PVM is characterized on measurable sets by $VM(S)V^*u=\mathbf1_Su$ almost everywhere. The state integral has all integrable matrix coefficients, and the dual images of every pair of bounded observables commute. This gives the continuous classical-quantum embedding without treating a Dirac position distribution as a normal Hilbert vector.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 4, §3, unnumbered continuous c-q embedding

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- Holevo arXiv:1211.4774v1, PDF pp.4-5: continuous-alphabet embedding.
The position observable is constructed as an actual multiplication PVM on L2.
Normal-state laws, the CPTP predual, its full dual multiplication action, and
all coefficient integrability are conclusions. No Dirac ket is a normal vector. -/
theorem continuous_cq_embedding {X I J : Type} [MeasurableSpace X]
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (mu : Measure X) [SigmaFinite mu]
    (V : Hilbert I ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 mu)
    (prepared : X → State J) (hprepared : Measurable prepared) :
    ∃ (M : HilbertPOVM (Hilbert I) X) (Phi : DualChannel I J)
      (law : State I → Measure X),
      (∀ (S : Set X), MeasurableSet S → ∀ u : Hilbert I,
        ∀ᵐ x ∂mu, (V (M.effect S u)) x = if x ∈ S then (V u) x else 0) ∧
      (∀ (S T : Set X), MeasurableSet S → MeasurableSet T →
        M.effect (S ∩ T) = (M.effect S).comp (M.effect T)) ∧
      (∀ rho : State I, law rho Set.univ = 1 ∧
        (∀ (S : Set X), MeasurableSet S → law rho S =
          ENNReal.ofReal (tracePair rho.coefficients (operatorCoeff (M.effect S))).re) ∧
        IsBarycenter (law rho) (fun x => (prepared x).coefficients)
          (Phi.predual.val rho.coefficients)) ∧
      (∀ (B : Hilbert J →L[ℂ] Hilbert J) (u : Hilbert I),
        ∀ᵐ x ∂mu, (V (Phi.dual B u)) x =
          tracePair (prepared x).coefficients (operatorCoeff B) * (V u) x) ∧
      IsCQ Phi := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end
