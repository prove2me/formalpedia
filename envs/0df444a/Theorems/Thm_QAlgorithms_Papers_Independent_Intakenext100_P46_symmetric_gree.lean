-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_symmetric_gree
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.symmetric_gree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:06:26.533989+00:00
-- url     : https://prove2.me/theorems/39ec32b0-9d73-4273-8bcb-fa20b56e953b
-- title:
--   §5, Eq. (41): symmetric Gaussian minimizer and two-variable GREE
-- statement:
--   Let $\rho$ be an entangled centered symmetric two-mode Gaussian density with covariance blocks $\tfrac12\begin{pmatrix}m&k_q\\k_q&m\end{pmatrix}$ and $\tfrac12\begin{pmatrix}m&-k_p\\-k_p&m\end{pmatrix}$ in the sign chart $k_q,k_p\ge0$. Its entropy $H(\rho)$ is finite, even when it has pure modes. For normal eigenvalues $\gamma_A,\gamma_B\ge1/2$, put $s_1=[4\gamma_A^2(4\gamma_B^2+1)/(4\gamma_A^2+1)]^{1/4}$, $s_2=[(4\gamma_B^2+1)/(4\gamma_B^2(4\gamma_A^2+1))]^{1/4}$ and $Q=2^{-1/2}\begin{pmatrix}s_1&s_2\\s_1&-s_2\end{pmatrix}$. Construct the border covariance $(Q\oplus Q^{-T})\operatorname{diag}(\gamma_A,\gamma_B,\gamma_A,\gamma_B)(Q\oplus Q^{-T})^T$, then apply $Y(y)^{-1}$ by covariance congruence, where $Y(y)=\operatorname{diag}(\sqrt y,\sqrt y,y^{-1/2},y^{-1/2})$ and $y>0$. Let $V_\rho(\gamma_A,\gamma_B)$ be the infimum of actual operator divergences to those densities as $y$ varies. There exist $\gamma_A,\gamma_B\ge1/2$, $y>0$ and an actual symmetric Gaussian border density attaining
--   $$E_{GR}(\rho)=D(\rho\Vert\sigma)=V_\rho(\gamma_A,\gamma_B)=\min_{a,b\ge1/2}V_\rho(a,b).$$
--   For the strict chart put $u=\ln((2\gamma_A+1)/(2\gamma_A-1))$ and $v=\ln((2\gamma_B+1)/(2\gamma_B-1))$. Then
--   $$V_\rho=-H(\rho)-\ln(2\sinh(u/2))-\ln(2\sinh(v/2))+\tfrac12\sqrt{(m+k_q)(m-k_p)u^2+(m-k_q)(m+k_p)v^2+(m-k_q)(m-k_p)uv\coth(u/2)\coth(v/2)+(m+k_q)(m+k_p)uv\tanh(u/2)\tanh(v/2)}.$$
--   Here $E_{GR}$ is the infimum of the actual Umegaki divergence $D$ over all separable Gaussian densities on the same cut, with trace-norm closed convex-hull separability. This gives the two-variable minimization. At singular parameters $V_\rho$ is defined through the constructed density and independent Umegaki divergence; no unsupported real logarithmic endpoint or finite optimizer is assumed. The common squeeze preserves exchange symmetry and must be retained when $k_q\ne k_p$.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 11, §5, Eq. (41): symmetric Gaussian minimizer and two-variable GREE

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

/-- Chen, PDF pp.9,11–12, (41): a symmetric Gaussian border attains GREE;
the resulting optimization has two normal-mode parameters. Endpoints are
operator-defined in symmetricValue, and its literal finite chart is (41).
Pure rho modes are allowed; no faithful-optimizer assumption is inserted. The
common local squeezing is retained when kq and kp differ. Printed on p.9:
symmetric states are called type (iii). Changed: use exchange symmetry, the
a=b/type-(iv) chart. Why: p.8 defines symmetry as type (iv), and the displayed
Eq. (12) and Eq. (41) use that covariance. -/
theorem symmetric_gree (rho : State (Occupation (Fin 1) × Occupation (Fin 1)))
    (m kq kp : ℝ) (hrho : HasGaussian rho 0 (symmetricCM m kq kp))
    (hkq : 0 ≤ kq) (hkp : 0 ≤ kp)
    (hentangled : ¬ IsSeparable rho.coefficients) :
    densityEntropy rho < ⊤ ∧
    (∃ (gA gB y : ℝ) (sigma : State (Occupation (Fin 1) × Occupation (Fin 1))),
      1 / 2 ≤ gA ∧ 1 / 2 ≤ gB ∧ 0 < y ∧
      HasGaussian sigma 0 (symmetricCandidateCM gA gB y) ∧ GaussianBorder sigma ∧
      operatorRelativeEntropy rho sigma = gree rho ∧ symmetricValue rho gA gB = gree rho ∧
      ∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b →
        symmetricValue rho gA gB ≤ symmetricValue rho a b) ∧
    (∀ gA gB : ℝ, 1 / 2 < gA → 1 / 2 < gB →
      symmetricValue rho gA gB = ENNReal.ofReal (-(densityEntropy rho).toReal +
        symmetricObjective m kq kp (modeEM gA) (modeEM gB))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
