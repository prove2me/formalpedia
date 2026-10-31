-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_14
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:49:09.340401+00:00
-- url     : https://prove2.me/theorems/b5424a16-8744-4991-812c-c62b89531a59
-- title:
--   Proposition 14A–B: local continuity of constrained Holevo capacity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Equip channels with strong convergence and states with trace norm. The constrained capacity $\overline C(\Phi,\rho)$ is jointly lower semicontinuous everywhere, and $\Delta(\Phi,\rho)=I(\Phi,\rho)-\overline C(\Phi,\rho)$ is jointly lower semicontinuous on $\overline C<\infty$. For $\Phi_n\to\Phi_0$ strongly and $\rho_n\to\rho_0$,
--
--   $$I(\Phi_n,\rho_n)\to I(\Phi_0,\rho_0)<\infty\quad\Longrightarrow\quad\overline C(\Phi_n,\rho_n)\to\overline C(\Phi_0,\rho_0)<\infty.$$
--   Both convergences hold if either input entropy converges to its finite limit or output entropy $S(\Phi_n(\rho_n))$ converges to its finite limit. No energy hypothesis is used.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 43, Proposition 14A–B: local continuity of constrained Holevo capacity

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

/-- arXiv:2304.05388v3, Proposition 14A–B, PDF pp.42–43. Strong channel and
trace-norm state topologies; both entropy sufficient alternatives are retained. -/
theorem proposition_14 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] :
    LowerSemicontinuous (fun p : Channel A B × State A => barycentricChi p.2.coefficients p.1.val) ∧
    LowerSemicontinuousOn (fun p : Channel A B × State A => constrainedInformationDeficit p.1.val p.2.coefficients)
      {p | barycentricChi p.2.coefficients p.1.val < ⊤} ∧
    (∀ (rho : ℕ → State A) (rho0 : State A) (Phi : ℕ → Channel A B) (Phi0 : Channel A B),
      Tendsto rho atTop (𝓝 rho0) → Tendsto Phi atTop (𝓝 Phi0) →
      ((Tendsto (fun n => mutualInformation (rho n).coefficients (Phi n).val) atTop
          (𝓝 (mutualInformation rho0.coefficients Phi0.val)) ∧
        mutualInformation rho0.coefficients Phi0.val < ⊤) →
       Tendsto (fun n => barycentricChi (rho n).coefficients (Phi n).val) atTop
          (𝓝 (barycentricChi rho0.coefficients Phi0.val)) ∧
        barycentricChi rho0.coefficients Phi0.val < ⊤) ∧
      (((Tendsto (fun n => extendedEntropyNats (rho n).coefficients) atTop
          (𝓝 (extendedEntropyNats rho0.coefficients)) ∧ extendedEntropyNats rho0.coefficients < ⊤) ∨
        (Tendsto (fun n => extendedEntropyNats ((Phi n).val (rho n).coefficients)) atTop
          (𝓝 (extendedEntropyNats (Phi0.val rho0.coefficients))) ∧
          extendedEntropyNats (Phi0.val rho0.coefficients) < ⊤)) →
       (Tendsto (fun n => mutualInformation (rho n).coefficients (Phi n).val) atTop
          (𝓝 (mutualInformation rho0.coefficients Phi0.val)) ∧ mutualInformation rho0.coefficients Phi0.val < ⊤) ∧
       (Tendsto (fun n => barycentricChi (rho n).coefficients (Phi n).val) atTop
          (𝓝 (barycentricChi rho0.coefficients Phi0.val)) ∧ barycentricChi rho0.coefficients Phi0.val < ⊤))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end
