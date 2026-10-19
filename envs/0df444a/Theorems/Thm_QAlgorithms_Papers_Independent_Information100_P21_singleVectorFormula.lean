-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_singleVectorFormula
-- name    : QAlgorithms.Papers.Independent.Information100.P21.singleVectorFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:52:15.992993+00:00
-- url     : https://prove2.me/theorems/996c7868-1f8c-435c-856d-556d8ad7c404
-- title:
--   III.10 — Theorem III.10 (Exact single-vector formula). For every two-qubit state ρ,
-- statement:
--   For every two-qubit density operator $\rho$, writing $\alpha_1(b)$ for the largest Schmidt coefficient of a unit vector $b$ and $[x]_+=\max(x,0)$,
--   $$R_s(\rho)=R_g(\rho)=\max_{\|b\|=1}\frac{[-\langle b|\rho^\Gamma|b\rangle]_+}{\alpha_1(b)^2}.$$
--   The maximum is attained. If $\rho$ is entangled and a rank-one standard-dual optimum has direction $b_*$, then $|b_*\rangle\langle b_*|/\alpha_1(b_*)^2$ is optimal in both dual problems. The unit-vector denominator lies between $1/2$ and $1$.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 9, III.10 — Theorem III.10 (Exact single-vector formula). For every two-qubit state ρ,

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 9, Theorem III.10 (Exact single-vector formula). For every two-qubit state ρ,. -/
theorem singleVectorFormula (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) :
  rs rho=rg rho ∧ IsGreatest {q : ℝ | ∃ b : Vec QQ, ‖b‖=1 ∧ q=quotient rho b} (rg rho) ∧
  (¬ sep rho → ∀ (b : Vec QQ) (w : ℝ) (P Q : Op QQ), ‖b‖=1 → 0<w →
    optDS rho ((w:ℂ) • proj b) P Q →
    optDG rho (((schmidtSq b)⁻¹:ℂ) • proj b) ∧
      ∃ P1 Q1 : Op QQ, optDS rho (((schmidtSq b)⁻¹:ℂ) • proj b) P1 Q1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
