-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_pure_state_entanglement_epr
-- name    : QAlgorithms.Papers.Independent.Next46.P45.pure_state_entanglement_epr
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:47:48.302975+00:00
-- url     : https://prove2.me/theorems/99d82c93-5933-44b1-bf25-dd7d4673f0f4
-- title:
--   Pure-state entanglement bounded by EPR uncertainty
-- statement:
--   Let $\psi$ be any normalized pure state of two genuine bosonic oscillator modes, without an energy or entropy restriction. Write $E(\psi)=S_2(\operatorname{Tr}_B|\psi\rangle\langle\psi|)$ for its extended spectral entropy in bits. Define
--
--   $$\Delta(\psi)=\min\!\left\{1,\frac{\operatorname{Var}_\psi(X_A-X_B)+\operatorname{Var}_\psi(P_A+P_B)}2\right\},\qquad r_t=-\tfrac12\ln t.$$
--
--   A variance is $+\infty$ outside the corresponding observable domain, and this gives $\Delta=1$ after clipping. For $r\ge0$, let $|\Psi_s(r)\rangle=\cosh(r)^{-1}\sum_{N\ge0}\tanh(r)^N|N,N\rangle$, including the vacuum at $r=0$. Then
--
--   $$E(\psi)\ge E\bigl(\Psi_s(r_{\Delta(\psi)})\bigr).$$
--
--   This relates operational EPR uncertainty to entanglement for arbitrary pure states, including those with infinite entanglement.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 2, Proposition 1: pure-state entanglement versus EPR uncertainty

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.2, Proposition 1; proof p.3: all normalized pure states, without a
finite-energy or finite-entropy hypothesis. Delta=1 selects the vacuum r=0. -/
theorem pure_state_entanglement_epr (psi : PureVector) :
    pureEntanglement (squeezedVector (squeezingAt (eprUncertainty psi.val))) ≤
      pureEntanglement psi.val := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
