-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P69_separableGaussianComparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P69.separableGaussianComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:37:29.637289+00:00
-- url     : https://prove2.me/theorems/d588f022-833a-4c43-bb55-129c49db977f
-- title:
--   Constructed separable Gaussian comparison for finite-resource REE
-- statement:
--   Use physical quadratures $(q_A,p_A,q_B,p_B)$ with $\hbar=1$ and vacuum covariance $I_4/2$. Let $\eta>0$ and $r\ge0$ be finite real numbers. Set
--   $$
--   \nu=\frac{e^{-2r}(\eta+1)}2,\qquad D=\eta+1-e^{2r}|\eta-1|,
--   $$
--   and assume $\nu\ge |\eta-1|/2$ and $D>0$. Define
--   $$
--   b=\frac{-|\eta-1|+\eta e^{2r}+e^{-2r}}{2D},\quad
--   a=\frac{2b+(\eta-1)e^{-2r}}{2\eta},\quad
--   c=\frac{2b-e^{-2r}}{2\sqrt\eta},\quad
--   c_{\rm sep}=\sqrt{(a-1/2)(b-1/2)}.
--   $$
--   Construct the centered Gaussian operators $\sigma_\nu$ and $\widetilde\sigma_{\rm sep}$ from the respective covariance matrices
--   $$
--   V=\begin{pmatrix}aI&cZ\\cZ&bI\end{pmatrix},\qquad
--   \widetilde V=\begin{pmatrix}aI&c_{\rm sep}Z\\c_{\rm sep}Z&bI\end{pmatrix},
--   \quad I=\operatorname{diag}(1,1),\quad Z=\operatorname{diag}(1,-1).
--   $$
--   Both constructed operators are normalized positive trace-class states of finite energy on the full two-mode bosonic Hilbert space, with these physical symmetric covariances. The comparison state is separable across $A:B$, and
--   $$
--   E_R(\sigma_\nu):=\inf_{\tau\ {
--   m separable}} S(\sigma_\nu\Vert\tau)
--   \le S(\sigma_\nu\Vert\widetilde\sigma_{\rm sep})=: \Psi(\mathcal E_{\eta,\nu}).
--   $$
--   Here $S$ is extended Umegaki relative entropy in bits and the infimum ranges over every normalized separable state, including non-Gaussian states. This supplies the explicit comparison value used by the paper's finite-resource bounds.
--
--   **Formalization Note** The operators are constructed by their full Weyl characteristics; validity and separability are conclusions. The vacuum extension at covariances without a Gaussian realization is never accepted as a substitute for these conclusions. The accepted characteristic uses doubled covariance, so the adapter supplies $2V$ and $2\widetilde V$. No operational capacity statement is included in this item.
-- source:
--   Finite-resource teleportation stretching for continuous-variable systems, arXiv:1706.06065v3, PDF p. 4, IV, Eqs. (28)–(29); resource Eqs. (8)–(11), p.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P69

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P69

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance covarianceCharacteristicValue
   multimodeWeylTrace standardFormCovariance vacuumKernel)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01 (generalizedRelativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.06065v3, PDF p.4, (28)--(29), with resource (8)--(11) on p.2.
Both Gaussian states are constructed from their CMs. Normalization, physical
covariance, finite energy, and separability of the comparison are conclusions.
This state comparison does not need or assert the deferred operational converse. -/
theorem separableGaussianComparison
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 ≤ r)
    (hnoise : |eta - 1| / 2 ≤ resourceNoise eta r)
    (hdenominator : 0 < resourceDenominator eta r) :
    CenteredGaussianAt (resourceCovariance eta r) (resourceKernel eta r) ∧
    CenteredGaussianAt (comparisonCovariance eta r) (comparisonKernel eta r) ∧
    IsSeparable (twoModeSplit (comparisonKernel eta r)) ∧
    relativeEntropyEntanglementBits (twoModeSplit (resourceKernel eta r)) ≤
      gaussianComparisonBound eta r := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P69

end
