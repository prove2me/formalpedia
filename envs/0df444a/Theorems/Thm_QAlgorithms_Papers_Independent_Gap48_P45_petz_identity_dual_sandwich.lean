-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_identity_dual_sandwich
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petz_identity_dual_sandwich
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:01:58.150456+00:00
-- url     : https://prove2.me/theorems/2bcb529e-53f0-4b5b-a198-104366847823
-- title:
--   Petz identity transferred to the dual channel: sandwich form
-- statement:
--   Let $\Phi$ be a channel and $\rho,\sigma$ states with the Petz identity $\rho=\mathcal R_{\sigma,\Phi}(\Phi(\rho))$. Write $s=\sigma^{1/2}$ and $t=\Phi(\sigma)^{1/2}$. If a bounded operator $B$ and $c>0$ satisfy $tBt=c\,\Phi(\rho)$, then
--
--   $$s\,\Phi^{*}(B)\,s=c\,\rho .$$
--
--   Role: turns each output operator $B_i$ (with $tB_it=\pi_i\Phi(\rho_i)$) into the input sandwich $s\Phi^*(B_i)s=\pi_i\rho_i$, which bounds the rank of $\Phi^*(B_i)$ by the rank of $\rho_i$ (general clause) and identifies $\Phi^*(B_i)$ as $|w_i\rangle\langle w_i|$ (pure clause).
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3 (PDF p. 8: the Petz identity rho_i = R(Phi(rho_i)) for the reference state rho-bar, equation (9), rewritten through the dual channel); Petz recovery map R_sigma(X) = sigma^{1/2} Phi*(Phi(sigma)^{-1/2} X Phi(sigma)^{-1/2}) sigma^{1/2} (D. Petz, Commun. Math. Phys. 105 (1986) 123-131)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

theorem petz_identity_dual_sandwich {I J : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho sigma : State I)
    (hP : rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients))
    (B : Hilbert J →L[ℂ] Hilbert J) (c : ℝ) (hc : 0 < c)
    (hB : (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
        (B.comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
      (c : ℂ) • boundedOperator (Phi.val rho.coefficients)) :
    (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
        ((channelDual Phi.val B).comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
      (c : ℂ) • boundedOperator rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
