-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_optimalNoiseStructure
-- name    : QAlgorithms.Papers.Independent.Information100.P21.optimalNoiseStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:53:36.801838+00:00
-- url     : https://prove2.me/theorems/0c4ff2bb-430c-4180-84a6-2fb8aeb255fe
-- title:
--   III.12 — Theorem III.12 (Optimal-noise structure). Let ρ be an entangled two-qubit state, write the common robustness as
-- statement:
--   Let $\rho$ be an entangled two-qubit state and let $b_*$ maximize the single-vector quotient. Choose ordered Schmidt coefficients $\alpha_1\ge\alpha_2\ge0$ and orthonormal Schmidt bases $u_j,f_j$. Then $R=R_s(\rho)=R_g(\rho)>0$, $\alpha_2>0$, and $W_*=|b_*\rangle\langle b_*|/\alpha_1^2$ is generalized-dual optimal.
--   $$\alpha_1>\alpha_2\ \Longrightarrow\ Y_*=R|u_1\otimes\overline f_1\rangle\langle u_1\otimes\overline f_1|.$$
--   In this case $Y_*$ is the unique generalized-primal optimum, and its normalized pure-product noise is unique and standard-admissible. If $\alpha_1=\alpha_2$, every generalized optimum only has the support restriction $\operatorname{ran}Y\subseteq\ker(I-W_*^\Gamma)$, whose dimension is three. No uniqueness or universal separability follows in that branch.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 10, III.12 — Theorem III.12 (Optimal-noise structure). Let ρ be an entangled two-qubit state, write the common robustness as

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 10, Theorem III.12 (Optimal-noise structure). Let ρ be an entangled two-qubit state, write the common robustness as. -/
theorem optimalNoiseStructure (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) (he : ¬sep rho)
  (b : Vec QQ) (hb : maximizer rho b) (a1 a2 : ℝ) (u f : Fin 2 → Vec (Fin 2))
  (hs : schmidt b a1 a2 u f) :
  0<rg rho ∧ rs rho=rg rho ∧ 0<a2 ∧
  optDG rho (((a1^2)⁻¹:ℂ) • proj b) ∧
  (a2<a1 → let omega := proj (tensor (u 0) (conjugate (f 0)))
    let Y := (rg rho:ℂ) • omega
    optG rho Y ∧ optS rho Y ∧ sep omega ∧ QAlgorithms.IsDensityMatrix omega ∧
    (∀ Z : Op QQ, optG rho Z → Z=Y) ∧
    (∀ eta : Op QQ, QAlgorithms.IsDensityMatrix eta → sep (mix rho eta (rg rho)) → eta=omega)) ∧
  (a1=a2 → let H := 1-pt (((a1^2)⁻¹:ℂ) • proj b)
    Module.finrank ℂ (LinearMap.ker (Matrix.toLin' H))=3 ∧
    ∀ Y : Op QQ, optG rho Y →
      LinearMap.range (Matrix.toLin' Y) ≤ LinearMap.ker (Matrix.toLin' H)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
