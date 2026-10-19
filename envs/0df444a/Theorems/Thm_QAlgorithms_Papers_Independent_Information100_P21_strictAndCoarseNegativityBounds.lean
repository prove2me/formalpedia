-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_strictAndCoarseNegativityBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P21.strictAndCoarseNegativityBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:08:24.476916+00:00
-- url     : https://prove2.me/theorems/2b153e9c-5d42-4cb8-8357-5cbe7131f215
-- title:
--   VII — strict eigenvector bound and state-only consequence
-- statement:
--   Let $\rho$ be an entangled two-qubit state, with negativity $\mathcal N$ and concurrence $C(\rho)>0$. Then
--   $$R_s(\rho)=R_g(\rho)\ge\frac{2\mathcal N}{1+\sqrt{1-[2\mathcal N/C(\rho)]^2}}.$$
--   For any unit negative eigenvector $v_-$, its pure concurrence satisfies $C_-\ge2\mathcal N/C(\rho)$. When $0<C_-<1$, the eigenvector lower bound $2\mathcal N/(1+\sqrt{1-C_-^2})$ is strictly less than the robustness. The auxiliary bound is credited to Ref. [15]; it is not a hypothesis or a claim that every point on a plotted frontier is attained.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 23, VII — strict eigenvector bound and state-only consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 23, strict eigenvector bound and state-only consequence. -/
theorem strictAndCoarseNegativityBounds (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) (he : ¬sep rho) :
  0<concurrence rho ∧
  2*QAlgorithms.Entanglement.negativity rho/(1+Real.sqrt (1-(2*QAlgorithms.Entanglement.negativity rho/concurrence rho)^2))≤rs rho ∧
  (∀ v : Vec QQ, ‖v‖=1 →
    (pt rho).mulVec (fun i => v i)=(-QAlgorithms.Entanglement.negativity rho:ℂ) • (fun i => v i) →
    2*QAlgorithms.Entanglement.negativity rho/concurrence rho≤pureConcurrence v ∧
    (0<pureConcurrence v → pureConcurrence v<1 →
      2*QAlgorithms.Entanglement.negativity rho/(1+Real.sqrt (1-pureConcurrence v^2))<rs rho)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
