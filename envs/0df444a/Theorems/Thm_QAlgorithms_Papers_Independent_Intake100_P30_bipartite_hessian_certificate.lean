-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_bipartite_hessian_certificate
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.bipartite_hessian_certificate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:50:49.45209+00:00
-- url     : https://prove2.me/theorems/feb7d566-6152-4cca-9e1c-d55d0477ca02
-- title:
--   IV.D: semidefinite Hessian certificate
-- statement:
--   Let $G=\begin{psmallmatrix}0&G_0^T\\G_0&0\end{psmallmatrix}$ with real square orthogonal $G_0$, and let $\alpha>0$. At $Z'=i\operatorname{sech}2\alpha I+\tanh2\alpha G$,
--
--   $$\operatorname{Im}[(I+Z'^2)\circ Z']=2\operatorname{sech}2\alpha\tanh^2 2\alpha\,[(I+G)\circ(I+G)]\ge0.$$
--
--   This is the exact semidefinite Hessian certificate. It does not establish a local or global minimum; the source explicitly leaves that stronger conclusion open.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 15, IV.D: semidefinite Hessian certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.15–16, (4.19): exact positive semidefinite Hessian
certificate only. The source expressly does not infer a local or global minimum. -/
theorem bipartite_hessian_certificate (n : ℕ) (G0 : Matrix (Fin n) (Fin n) ℝ)
    (hLeft : G0.transpose * G0 = 1) (hRight : G0 * G0.transpose = 1) (alpha : ℝ) (hAlpha : 0 < alpha) :
    let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.fromBlocks 0 G0.transpose G0 0
    phaseHessian (sechGraph G alpha) =
      (2 * (Real.cosh (2*alpha))⁻¹ * (Real.tanh (2*alpha))^2) •
        (fun j k => ((1 + G) j k)^2) ∧
    (phaseHessian (sechGraph G alpha)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
