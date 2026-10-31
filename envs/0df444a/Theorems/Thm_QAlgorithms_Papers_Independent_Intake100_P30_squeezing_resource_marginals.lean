-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_squeezing_resource_marginals
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.squeezing_resource_marginals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:49:12.047409+00:00
-- url     : https://prove2.me/theorems/00fe1cca-f213-4f0c-9883-960e66c4dec4
-- title:
--   IV.C: squeezing efficiency in one-mode marginals
-- statement:
--   For a valid $Z=V+iU$, isotropy of every single-mode covariance marginal is equivalent to
--
--   $$(U+VU^{-1}V-U^{-1})_{jj}=0,\qquad (VU^{-1})_{jj}=0\quad\text{for all }j.$$
--
--   The two-mode H-graph cluster representative $Z'=i\operatorname{sech}2\alpha I+\tanh2\alpha G$ satisfies this condition for $\alpha>0$, where $G$ is the two-mode unit edge. The canonical representative $G+i e^{-2r}I$ fails it at every finite real $r$: the first displayed diagonal difference equals $e^{-2r}$. This is precisely the paper's marginal squeezing-resource criterion.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 15, IV.C: squeezing efficiency in one-mode marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.15, (4.12)–(4.13): marginal isotropy is the exact
squeezing-resource criterion here. No gate-count or preparation optimum is claimed. -/
theorem squeezing_resource_marginals {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (hZ : ValidGraph Z) (alpha r : ℝ) (hAlpha : 0 < alpha) :
    (HasIsotropicMarginals Z ↔ ∀ j,
      (imagPart Z + realPart Z * (imagPart Z)⁻¹ * realPart Z - (imagPart Z)⁻¹) j j = 0 ∧
      (realPart Z * (imagPart Z)⁻¹) j j = 0) ∧
    HasIsotropicMarginals (sechGraph twoEdge alpha) ∧
    ¬ HasIsotropicMarginals (canonicalGraph twoEdge r) ∧
    (∀ j : Fin 2,
      let H := canonicalGraph twoEdge r
      (imagPart H + realPart H * (imagPart H)⁻¹ * realPart H - (imagPart H)⁻¹) j j =
        Real.exp (-2*r)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
