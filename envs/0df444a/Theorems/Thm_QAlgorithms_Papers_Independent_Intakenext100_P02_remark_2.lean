-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_remark_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.remark_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:14:16.150904+00:00
-- url     : https://prove2.me/theorems/3764aace-9d29-46e2-b978-cd796165f040
-- title:
--   Remark 2: dimension-bound entropy-reduction witnesses
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let A and B be finite nonzero systems and let d=dim H_B. For every rank-one discrete M, the chaotic state rho=I/(d dim H_A) and every pure sigma satisfy
--
--   $$R_M(\rho)=S(\rho_B)=\ln d,\quad R_M(\sigma)=0,\quad\tfrac12\|\rho-\sigma\|_1=1-\frac1{d\dim H_A}.$$
--   For two d-dimensional systems, take rho=d^(-1) sum_i |ii><ii|, sigma=|jj><jj| and the matching computational measurement, where j is any basis index. Then R_M(rho)=ln d, R_M(sigma)=0 and their trace distance is 1-1/d. The support of rho, hence the joint support span with sigma, has dimension d. These are both explicit dimension-bound witness families, including the singleton case.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 11, Remark 2: dimension-bound entropy-reduction witnesses

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

/-- arXiv:2304.05388v3, Remark 2, PDF p.11. Both explicit witness families,
with exact ER values and trace distances, including d=1. -/
theorem remark_2 {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (∀ (K : Type) [Countable K] (M : DiscretePOVM B K), HasRankOneEffects M →
      ∀ psi : PureState (A × B),
        localER M (uniformDensityCoefficients (A × B)) = ENNReal.ofReal (Real.log (Fintype.card B)) ∧
        extendedEntropyNats (traceFirst (uniformDensityCoefficients (A × B))) = ENNReal.ofReal (Real.log (Fintype.card B)) ∧
        localER M psi.val.coefficients = 0 ∧
        (traceSize (uniformDensityCoefficients (A × B) - psi.val.coefficients)).toReal / 2 =
          1 - 1 / ((Fintype.card A : ℝ) * Fintype.card B)) ∧
    (∀ (d : ℕ) (i : Fin d) (M : DiscretePOVM (Fin d) (Fin d)),
      (∀ k a b, operatorCoeff (M.effect k) a b = if a = k ∧ b = k then 1 else 0) →
      localER M (correlatedUniform d) = ENNReal.ofReal (Real.log d) ∧
      localER M (diagonalPure i) = 0 ∧
      (traceSize (correlatedUniform d - diagonalPure i)).toReal / 2 = 1 - 1 / (d : ℝ) ∧
      QAlgorithms.Papers.Independent.Gap48.P45.operatorRank (boundedOperator (correlatedUniform d)) = (d : ℕ∞)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end
