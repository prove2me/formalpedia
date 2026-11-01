-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_tmst_gree
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.tmst_gree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:07:08.180014+00:00
-- url     : https://prove2.me/theorems/e9e10ce4-393d-47b3-b60c-f91638c3fb92
-- title:
--   §5, Eq. (42): symmetric two-mode squeezed thermal minimizer and one-variable GREE
-- statement:
--   Let $\rho$ be an entangled centered symmetric two-mode squeezed thermal state, with covariance blocks $\tfrac12\begin{pmatrix}m&k\\k&m\end{pmatrix}$ and $\tfrac12\begin{pmatrix}m&-k\\-k&m\end{pmatrix}$, where $k\ge0$. Pure inputs are allowed; $H(\rho)$ denotes the finite spectral entropy in nats, $D$ is Umegaki divergence, and $E_{GR}$ is its infimum over all separable Gaussian densities on the same cut. There is a finite $u>0$ and a separable TMST Gaussian border density $\sigma$ with equal EM normal parameters $u$ such that
--   $$E_{GR}(\rho)=D(\rho\Vert\sigma)=-H(\rho)+\min_{v>0}f_{m,k}(v),$$
--   $$f_{m,k}(v)=-2\ln(2\sinh(v/2))+\frac v2[(m-k)\coth(v/2)+(m+k)\tanh(v/2)].$$
--   The minimum is achieved at $v=u$. If $\gamma=\tfrac12\coth(u/2)$, the attaining covariance has half-covariance parameters $m_\sigma=2\gamma^2+1/2$ and $k_{q,\sigma}=k_{p,\sigma}=2\gamma^2-1/2$. This is the one-variable reduction of Eq. (41). Entanglement excludes the separable-vacuum case with its nonattained infinite-parameter endpoint.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 11, §5, Eq. (42): symmetric two-mode squeezed thermal minimizer and one-variable GREE

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF p.11, (42), p.12: entangled symmetric TMST inputs have a TMST
border minimizer with equal finite EM eigenvalues. The displayed one-variable
minimum is attained, and input purity is allowed. Separable vacuum is excluded
by entanglement, not assigned a spurious finite-u minimum. -/
theorem tmst_gree (rho : State (Occupation (Fin 1) × Occupation (Fin 1)))
    (m k : ℝ) (hrho : HasGaussian rho 0 (symmetricCM m k k))
    (hk : 0 ≤ k) (hentangled : ¬ IsSeparable rho.coefficients) :
    densityEntropy rho < ⊤ ∧
    ∃ (u : ℝ) (sigma : State (Occupation (Fin 1) × Occupation (Fin 1))),
      0 < u ∧ HasGaussian sigma 0 (tmstBorderCM u) ∧ GaussianBorder sigma ∧
      operatorRelativeEntropy rho sigma = gree rho ∧
      gree rho = ENNReal.ofReal (-(densityEntropy rho).toReal + tmstObjective m k u) ∧
      ∀ v : ℝ, 0 < v → tmstObjective m k u ≤ tmstObjective m k v := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
