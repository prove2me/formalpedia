-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_71_74
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_71_74
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:33:45.286639+00:00
-- url     : https://prove2.me/theorems/292b43f0-2d38-4205-bc28-6bcd47f626ad
-- title:
--   Channel forms of the generalized correlation relations (71)–(74)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Given an actual dilation $V:A\to BE$ of a channel $\Phi$ and its complement $\widehat\Phi$, and a purification $\widehat\rho_{AR}$ of $\rho$, construct $\omega=(V\otimes I_R)\widehat\rho(V^*\otimes I_R)$. Then
--
--   $$I(\Phi,\rho)=I(B:R)_\omega=I(B:R)_{(\Phi\otimes\mathrm{Id})(\widehat\rho)},\quad \overline C(\Phi,\rho)=\chi_B(\omega_{BE})=C_R(\omega_{BR})=C_R((\Phi\otimes\mathrm{Id})(\widehat\rho)).$$
--   When $\overline C(\Phi,\rho)<\infty$, both corresponding $D_R$ quantities equal $I(\Phi,\rho)-\overline C(\Phi,\rho)$. Also $\overline C(\widehat\Phi,\rho)=\chi_E(\omega_{BE})=C_R(\omega_{ER})$ equals the supremum of $\mathrm{ER}(\omega_{BR},I_B\otimes M)$ over all discrete $M$ on $R$, equivalently over rank-one $M$, and equivalently using the actual channel output state instead of $\omega_{BR}$. Every complementary choice gives the same constrained capacity. The positive equalities permit infinity without finite input entropy.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 26, Channel forms of the generalized correlation relations (71)–(74)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P02

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel Complementary Purifies traceFirst traceSecond mutualInformation
   barycentricChi CountableStateEnsemble Barycenter convexOperatorMixture channelTensorAction)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (IsQuantumOperation operatorTrace StronglyConverges TraceNormConverges)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Gap48.P45
  (boundedTracePair dimensionCount generatedSpace outputSpace coefficientTraceHasSum)

open QAlgorithms.Papers.Independent.Renew46.P08 (qmi)

open QAlgorithms.Papers.Independent.Claimed50.P18 (swapCoeff associateRight dropMiddle)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2304.05388v3, channel relations (71)–(74), PDF pp.26–27. The joint
state is COMPUTED. Positive identities have no finite-entropy premise; (73)
uses only finite constrained Holevo information. -/
theorem eq_71_74 {A B E R : Type} [Countable A] [Countable B] [Countable E] [Countable R]
    [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (Phi : Channel A B) (PhiC : Channel A E)
    (V : Hilbert A →ₗᵢ[ℂ] Hilbert (B × E))
    (hV : ∀ rho : State A,
      Phi.val rho.coefficients = traceSecond (conjugateCoeff V.toContinuousLinearMap rho.coefficients) ∧
      PhiC.val rho.coefficients = traceFirst (conjugateCoeff V.toContinuousLinearMap rho.coefficients))
    (rho : State A) (psi : PureState (A × R)) (hpsi : Purifies psi rho.coefficients) :
    let omega := purifiedDilationCoefficients V psi
    mutualInformation rho.coefficients Phi.val = qmi (tripartiteAC omega) ∧
    qmi (tripartiteAC omega) = qmi (tensorApply Phi.val psi.val.coefficients) ∧
    barycentricChi rho.coefficients Phi.val = chiA (traceSecond omega) ∧
    barycentricChi rho.coefficients Phi.val = discreteClassicalCorrelation (tripartiteAC omega) ∧
    discreteClassicalCorrelation (tripartiteAC omega) = discreteClassicalCorrelation (tensorApply Phi.val psi.val.coefficients) ∧
    (barycentricChi rho.coefficients Phi.val < ⊤ →
      discreteOptimizedDiscord (tensorApply Phi.val psi.val.coefficients) = discreteOptimizedDiscord (tripartiteAC omega) ∧
      discreteOptimizedDiscord (tripartiteAC omega) = constrainedInformationDeficit Phi.val rho.coefficients) ∧
    barycentricChi rho.coefficients PhiC.val = chiA (swapCoeff (traceSecond omega)) ∧
    barycentricChi rho.coefficients PhiC.val = discreteClassicalCorrelation (traceA omega) ∧
    barycentricChi rho.coefficients PhiC.val =
      (⨆ (K : Type) (_ : Countable K) (M : DiscretePOVM R K), localER M (tripartiteAC omega)) ∧
    barycentricChi rho.coefficients PhiC.val =
      (⨆ (K : Type) (_ : Countable K) (M : DiscretePOVM R K), localER M (tensorApply Phi.val psi.val.coefficients)) ∧
    barycentricChi rho.coefficients PhiC.val =
      (⨆ (K : Type) (_ : Countable K) (M : {M : DiscretePOVM R K // HasRankOneEffects M}),
        localER M.val (tensorApply Phi.val psi.val.coefficients)) ∧
    (∀ (F : Type) [Countable F] [Nonempty F] (other : Channel A F),
      Complementary Phi other → barycentricChi rho.coefficients other.val =
        barycentricChi rho.coefficients PhiC.val) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end
