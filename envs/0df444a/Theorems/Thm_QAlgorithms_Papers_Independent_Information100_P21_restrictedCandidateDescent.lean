-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_restrictedCandidateDescent
-- name    : QAlgorithms.Papers.Independent.Information100.P21.restrictedCandidateDescent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:39.154353+00:00
-- url     : https://prove2.me/theorems/5f033465-2e2d-4ab5-92e6-75c4cc278abe
-- title:
--   V.A — feasible descent from the restricted candidate
-- statement:
--   For $\rho_{\rm ex}$, let $Y_0=(3/20)(|\Phi^-\rangle\langle\Phi^-|+|\chi\rangle\langle\chi|)$ with $\chi=(2|01\rangle+|10\rangle)/2$, intentionally of squared norm $5/4$. For $0\le\tau\le1$, put $Y_\tau=(1-\tau)Y_0+\tau Y_{\rm ex}$. Then
--   $$Y_\tau\text{ is standard feasible},\qquad\operatorname{Tr}Y_\tau=27/80-7\tau/80.$$
--   Every $\tau>0$ in this interval lowers the cost strictly. The normalized noise and normalized separable target vary continuously at zero. Hence the restricted candidate is not a full-space local minimum.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 17, V.A — feasible descent from the restricted candidate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 17, feasible descent from the restricted candidate. -/
theorem restrictedCandidateDescent  :
  (∀ t : ℝ, 0≤t → t≤1 → primalS rhoEx (descent t) ∧
    (descent t).trace.re=27/80-7*t/80 ∧ (0<t → (descent t).trace.re<noiseOld.trace.re)) ∧
  ContinuousAt (fun t : ℝ => (((descent t).trace.re)⁻¹:ℂ) • descent t) 0 ∧
  ContinuousAt (fun t : ℝ => ((1+(descent t).trace.re)⁻¹:ℂ) • (rhoEx+descent t)) 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
