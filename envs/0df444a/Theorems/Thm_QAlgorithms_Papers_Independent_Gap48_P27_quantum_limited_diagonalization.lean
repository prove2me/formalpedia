-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_quantum_limited_diagonalization
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.quantum_limited_diagonalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:22:05.436682+00:00
-- url     : https://prove2.me/theorems/016e3517-5d5d-4f72-8a40-84bfcb78f141
-- title:
--   §2: passive diagonalization of quantum-limited channels
-- statement:
--   Let $\Phi$ be a finite-mode quantum-limited attenuator, quantum-limited amplifier, or quantum-limited gauge-contravariant channel. There exist a channel $\Phi_c$ of the same type, nonnegative rectangular diagonal gain $K_c$, diagonal output noise, and passive input/output Fock unitaries $U_A,U_B$ such that
--
--   $$
--   \Phi[X]=U_B\Phi_c[U_A^*XU_A]U_B^*
--   \quad\text{for every trace-class }X.
--   $$
--
--   More precisely, for mode unitaries $V_A,V_B$, the covariant factorization is $K=V_BK_cV_A$ and the contravariant factorization is $K=V_BK_c\overline{V_A}$. The chosen Fock unitaries satisfy $U_A^*D(z)U_A=D(V_Az)$ and $U_B^*D(w)U_B=D(V_B^*w)$, preserve the vacuum, and the noise transforms as $\mu=V_B\mu_cV_B^*$. These identities give the dimensionally correct passive normal form, including unused input or output modes.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 6, §2: passive diagonalization of quantum-limited channels

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P27

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P27

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne
   productCoeff tensorApply traceSize BreaksTraceClassEntanglement)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats GeneralizedEnsemble HasAverage
   finiteEnsembleCapacity ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel vacuum productCoherentKernel modeEnergy husimi FockPOVM
   realFockTracePair)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassTensorMap traceClassChannelPower)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation partialRight partialLeft isometryCoeff conjugateKernel)

/-- §2, PDF pp.6-7, (11): passive diagonalization for all three limited
classes, with rectangular gains allowed. The dimensionally interchanged A/B
annihilation identities printed below (11) are replaced by Weyl intertwining. -/
theorem quantum_limited_diagonalization {a b : ℕ} (G : GaugeChannel a b)
    (hG : quantumLimitedAttenuator G ∨ quantumLimitedAmplifier G ∨
      quantumLimitedContravariant G) :
    diagonalizableGaugeChannel G := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
