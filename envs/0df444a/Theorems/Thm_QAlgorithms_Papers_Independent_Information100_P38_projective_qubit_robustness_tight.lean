-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_projective_qubit_robustness_tight
-- name    : QAlgorithms.Papers.Independent.Information100.P38.projective_qubit_robustness_tight
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:08:23.11934+00:00
-- url     : https://prove2.me/theorems/4aee7dd7-6d08-4fce-839e-9ec9cb499945
-- title:
--   Example 1
-- statement:
--   Let $H=E|1\rangle\langle1|$ with $E>0$, and let $M_\pm=(I\pm\mathbf m\cdot\boldsymbol\sigma)/2$ with $|\mathbf m|=1$. This is a POVM and
--
--   $$A_H^M=\frac E2\sqrt{m_x^2+m_y^2}=\frac E2C_{\ell_\infty}(M)=\frac E2R_C(M).$$
--
--   Here $C_{\ell_\infty}(M)=\max_{i<j}\sum_\mu|(M_\mu)_{ij}|$ and $R_C$ is measurement coherence robustness. The equality includes $m_x=m_y=0$ without normalizing a zero vector. It establishes tightness of the robustness upper bound for every rank-one projective qubit measurement.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 7, Example 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper pp.7–8, Example 1: every rank-one projective qubit measurement attains the
robustness bound; the zero-transverse-component case is included without division. -/
theorem projective_qubit_robustness_tight (E : ℝ) (hE : 0 < E)
    (m : Fin 3 → ℝ) (hm : ergotropicBlochLengthSquared m = 1) :
    let M := ergotropicBlochMeasurement m
    IsPOVM M ∧ observationalAdvantage ![0, E] M = E / 2 * Real.sqrt ((m 0)^2 + (m 1)^2) ∧
      observationalAdvantage ![0, E] M = E / 2 * measurementLinfCoherence M ∧
      observationalAdvantage ![0, E] M = E / 2 * measurementCoherenceRobustness M := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
