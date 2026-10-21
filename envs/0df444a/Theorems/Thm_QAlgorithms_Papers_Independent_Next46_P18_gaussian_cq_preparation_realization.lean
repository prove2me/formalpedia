-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_gaussian_cq_preparation_realization
-- name    : QAlgorithms.Papers.Independent.Next46.P18.gaussian_cq_preparation_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:10:36.946909+00:00
-- url     : https://prove2.me/theorems/847a464f-c50f-4e6f-8826-962499f45565
-- title:
--   §3, unnumbered Gaussian preparation realization
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Assume $K^{\mathsf T}\Delta_AK=0$ and put $\mathcal X=\operatorname{Ran}K^{\mathsf T}$. There is a sharp joint PVM $M$ for $R_AK$, identified by its characteristic $W_A(Kw)$, whose support is exactly $\mathcal X$. Its normal-state laws $\mu_\rho$ are probability measures supported on $\mathcal X$. There is a measurable field of normalized output densities $\rho_z$ with mean $z$ and covariance $\alpha$, specified on $\mathcal X$ by
--
--   $$\operatorname{Tr}(\rho_zW_B(w))=\exp\!\left(iz^{\mathsf T}w-\tfrac12w^{\mathsf T}\alpha w\right),\qquad \Phi(\rho)=\int\rho_z\,\mu_\rho(dz).$$
--
--   For every $z\in\mathcal X$ there are normal input states $\rho_n$ such that $\mu_{\rho_n}$ converges weakly to $\delta_z$, tested against every bounded continuous real function. This includes $K=0$, when the signal support is the singleton $\{0\}$. The realization explains the channel as Gaussian preparation driven by its commuting input observables.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 5, §3, unnumbered Gaussian preparation realization

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

/-- Holevo arXiv:1211.4774v1, PDF p.5: sharp Gaussian c-q realization.
The joint PVM is identified by its Weyl characteristic and its exact support.
Prepared states are indexed by physical mean through their characteristic
functions, correcting the printed W(z) displacement-coordinate mismatch.
All normal-state laws and the concentrating input sequence are conclusions. -/
theorem gaussian_cq_preparation_realization {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha)
    (hisotropic : K.transpose * (physicalCommutationMatrix s 1) * K = 0) :
    ∃ (M : HilbertPOVM (Hilbert I) (InterleavedPhase t))
      (law : State I → Measure (InterleavedPhase t))
      (prepared : InterleavedPhase t → State J),
      (∀ (S T : Set (InterleavedPhase t)), MeasurableSet S → MeasurableSet T →
        M.effect (S ∩ T) = (M.effect S).comp (M.effect T)) ∧
      (∀ (w : InterleavedPhase t) (u : Hilbert I),
        Integrable (fun z : InterleavedPhase t => Complex.exp (Complex.I * ((dotProduct z w : ℝ) : ℂ))) (M.law u) ∧
        inner ℂ u (WA.operator (K.mulVec w) u) =
          ∫ z : InterleavedPhase t, Complex.exp (Complex.I * ((dotProduct z w : ℝ) : ℂ)) ∂M.law u) ∧
      (∀ z : InterleavedPhase t, z ∈ Set.range K.transpose.mulVec ↔
        ∀ U : Set (InterleavedPhase t), IsOpen U → z ∈ U → M.effect U ≠ 0) ∧
      Measurable prepared ∧
      (∀ z ∈ Set.range K.transpose.mulVec, ∀ w,
        weylTraceCharacteristic WB (prepared z).coefficients w = gaussianFunction z alpha w) ∧
      (∀ rho : State I, law rho Set.univ = 1 ∧
        law rho (Set.range K.transpose.mulVec)ᶜ = 0 ∧
        (∀ S : Set (InterleavedPhase t), MeasurableSet S → law rho S =
          ENNReal.ofReal (tracePair rho.coefficients (operatorCoeff (M.effect S))).re) ∧
        IsBarycenter (law rho) (fun z => (prepared z).coefficients)
          (Phi.predual.val rho.coefficients)) ∧
      (∀ z ∈ Set.range K.transpose.mulVec, ∃ rho : ℕ → State I,
        ∀ f : InterleavedPhase t →ᵇ ℝ,
          Tendsto (fun n => ∫ x, f x ∂law (rho n)) atTop (𝓝 (f z))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end
