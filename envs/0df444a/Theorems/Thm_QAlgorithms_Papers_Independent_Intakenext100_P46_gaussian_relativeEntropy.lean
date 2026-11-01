-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_gaussian_relativeEntropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.gaussian_relativeEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:02:08.622657+00:00
-- url     : https://prove2.me/theorems/6927bdbf-c8bb-44df-80f2-3c2f881730bd
-- title:
--   §3, Eqs. (17),(18),(22): actual Gaussian relative entropy from CM and EM
-- statement:
--   Let $\rho$ and $\sigma$ be centered Gaussian density operators on a positive finite number of complete bosonic modes. Use any split into two registers; either register may be empty, so single-mode states are included. The input covariance is $\alpha$ and may have pure modes. Suppose the covariance of $\sigma$ is $S\operatorname{diag}(\gamma,\gamma)S^T$, with $S$ symplectic and every $\gamma_j>1/2$. Put $m_j=\ln((2\gamma_j+1)/(2\gamma_j-1))$, $M=S^{-T}\operatorname{diag}(m,m)S^{-1}$, and $\beta=S^{-1}\alpha S^{-T}$. The input spectral entropy $H(\rho)$ is finite. The reciprocal partition function is
--   $$c=\prod_j2\sinh(m_j/2)=\prod_j(\gamma_j^2-1/4)^{-1/2}>0.$$
--   The independently defined operator divergence satisfies
--   $$D(\rho\Vert\sigma)=-H(\rho)-\ln c+\tfrac12\operatorname{tr}(\alpha M)=-H(\rho)-\sum_j\ln(2\sinh(m_j/2))+\tfrac12\sum_j(\beta_{jj}+\beta_{n+j,n+j})m_j.$$
--   All logarithms are natural. This evaluates the actual divergence rather than defining it through covariances. If $\nu_j\ge\tfrac12$ are the symplectic eigenvalues of the input covariance, the independently defined spectral entropy also satisfies $$H(\rho)=\sum_j g(\nu_j-\tfrac12),\qquad g(t)=(t+1)\ln(t+1)-t\ln t,\quad g(0)=0.$$ The conclusion identifies the comparison density with its actual normalized Gibbs exponential, rather than assigning an exponential-matrix label only to its covariance.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 4, §3, Eqs. (17),(18),(22): actual Gaussian relative entropy from CM and EM

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

/-- Chen, PDF pp.4–5, (17),(18),(22): actual operator relative entropy equals
the CM/EM expression, including a single mode (one register may be empty).
rho may have pure normal modes. sigma alone is in the
finite exponential chart. The actual Gibbs density and Gaussian spectral entropy
are identified, and both the matrix trace and the normal-mode sum are given. -/
theorem gaussian_relativeEntropy {A B : Type} [Fintype A] [Fintype B]
    [Nonempty (A ⊕ B)]
    (rho sigma : State (Occupation A × Occupation B))
    (alpha : ModeMatrix (A ⊕ B)) (S : ModeMatrix (A ⊕ B)) (g : (A ⊕ B) → ℝ)
    (hrho : HasGaussian rho 0 alpha) (hS : IsSymplecticMatrix S)
    (hg : ∀ j, 1 / 2 < g j)
    (hsigma : HasGaussian sigma 0 (S * normalDiagonal g * S.transpose)) :
    let M := emFrom S g
    let c := normalization g
    let beta := S⁻¹ * alpha * S.transpose⁻¹
    densityEntropy rho < ⊤ ∧ HasFiniteEM (joinedCoefficients sigma.coefficients) M ∧
      (∃ (Sr : ModeMatrix (A ⊕ B)) (gr : (A ⊕ B) → ℝ),
        IsSymplecticMatrix Sr ∧ (∀ j, 1 / 2 ≤ gr j) ∧
        alpha = Sr * normalDiagonal gr * Sr.transpose ∧
        densityEntropy rho = ENNReal.ofReal (∑ j, bosonic (gr j - 1 / 2))) ∧
      0 < c ∧
      c = ∏ j, (Real.sqrt ((g j) ^ 2 - 1 / 4))⁻¹ ∧
      operatorRelativeEntropy rho sigma = ENNReal.ofReal
        (- (densityEntropy rho).toReal + covarianceObjective alpha M c) ∧
      operatorRelativeEntropy rho sigma = ENNReal.ofReal
        (- (densityEntropy rho).toReal - ∑ j, Real.log (2 * Real.sinh (modeEM (g j) / 2)) +
          (∑ j, (beta (Sum.inl j) (Sum.inl j) +
            beta (Sum.inr j) (Sum.inr j)) * modeEM (g j)) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
