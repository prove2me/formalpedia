-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_jc_visibility_gap
-- name    : QAlgorithms.Papers.Independent.Information100.P41.jc_visibility_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:32:44.864102+00:00
-- url     : https://prove2.me/theorems/26c78491-092a-4626-89c3-838b555400e6
-- title:
--   Visibility monotonicity and strict interior gap
-- statement:
--   Fix $\bar n=1/2$ and $\theta=\pi/2$ in the resonant JC experiment with a ground atom and a single-rail field whose real visibility is $0\le\eta\le1$. Let $R_\eta$ be the atomic output of the exact isometry and field partial trace, $A_\eta=\operatorname{Tr}((DR_\eta)^{-1}(R_\eta-DR_\eta)R_\eta)$, and $\Delta C_\eta=C(R_\eta)-C(|g\rangle\langle g|)$, with energy-basis dephasing $D$ and natural-log entropy. Define $G(\eta)=\ln(1+\operatorname{Re}A_\eta)-\Delta C_\eta$. Then
--
--   $$A_\eta=\eta^2,\qquad G(\eta)>0\quad(0<\eta<1),\qquad G(0)=G(1)=0,\qquad\Delta C_0=0.$$
--
--   The anomaly is nondecreasing on $[0,1]$. These statements express visibility-dependent coherence transfer and endpoint saturation; the zero-visibility assertion concerns this initially ground atom.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 4, Visibility dependence, pp.4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF pp.4–5: visibility dependence, strict interior gap, endpoint closure, and zero
transfer from the dephased field, at equal populations and pi/2. -/
theorem jc_visibility_gap :
    (∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      jcAnomaly eta (1 / 2) (Real.pi / 2) = ((eta ^ 2 : ℝ) : ℂ)) ∧
    MonotoneOn (fun eta : ℝ => (jcAnomaly eta (1 / 2) (Real.pi / 2)).re) (Set.Icc 0 1) ∧
    (∀ eta : ℝ, 0 < eta → eta < 1 → 0 < visibilityGap eta) ∧
    visibilityGap 0 = 0 ∧ visibilityGap 1 = 0 ∧
    jcChange 0 (1 / 2) (Real.pi / 2) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
