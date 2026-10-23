-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_incommensuratePair
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.incommensuratePair
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:09:10.178641+00:00
-- url     : https://prove2.me/theorems/8d8d9fbb-4894-4d91-be12-1c5a1fe40440
-- title:
--   Existence of an explicit incomparable Gaussian pair
-- statement:
--   For real $a,b,c,d$, let
--   $$
--   N(a,b,c,d)=\begin{pmatrix}a&0&c&0\\0&a&0&d\\c&0&b&0\\0&d&0&b\end{pmatrix}
--   $$
--   be the two-mode normal covariance, in the order $(X_1,P_1,X_2,P_2)$ with $\hbar=1$ and vacuum covariance $I$. There exist actual normalized Gaussian oscillator states $\rho,\rho'$ with finite second moments such that
--   $$
--   \Gamma_\rho=N(2,2,1,1),\qquad
--   \Gamma_{\rho'}=N(2,2,1,-1/2),
--   $$
--   $$
--   \rho\not\longrightarrow\rho'\text{ under LOG},\qquad
--   \rho'\not\longrightarrow\rho\text{ under LOG}.
--   $$
--   LOG denotes products of independent local Gaussian channels implemented by finite Gaussian ancillas, local Gaussian unitaries and partial traces. The negative final correlation is part of the example.
--
--   This establishes non-totality of operational convertibility without asserting antisymmetry on raw states.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 4, Application: incommensurate states

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, explicit application: actual Gaussian states with the two
specified normal covariances exist and are incomparable in BOTH directions.
The negative fourth coordinate is retained; Proposition 2 is not extended. -/
theorem incommensuratePair :
    ∃ rho target : TwoModeGaussianDensity,
      rho.covariance = standardFormCovariance 2 2 1 1 ∧
      target.covariance = standardFormCovariance 2 2 1 (-(1 / 2)) ∧
      ¬ LOGReachable rho target ∧ ¬ LOGReachable target rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
