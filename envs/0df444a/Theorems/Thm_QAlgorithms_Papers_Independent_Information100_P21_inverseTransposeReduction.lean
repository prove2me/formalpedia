-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_inverseTransposeReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P21.inverseTransposeReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:54:50.722667+00:00
-- url     : https://prove2.me/theorems/a5ca3f9a-b92f-49ef-98d9-8d82d807b6ca
-- title:
--   III.14 — Proposition III.14 (Inverse partial-transpose reduction). Let ρ be an entangled two-qubit state and put A = ρΓ . Let
-- statement:
--   Let $\rho$ be entangled on two qubits and $A=\rho^\Gamma$. The matrix $A$ is invertible. Let $q_{\min}$ be the attained minimum of $\langle p|A^{-1}|p\rangle$ over unit product vectors, and let $R_{\rm prod}$ be the infimum of nonnegative $t$ with $A+t|p\rangle\langle p|\succeq0$, using $+\infty$ for an empty feasible set. Then
--   $$q_{\min}<0\Longrightarrow R_{\rm prod}=-1/q_{\min},\qquad q_{\min}\ge0\Longrightarrow R_{\rm prod}=+\infty.$$
--   The second case admits no finite update. The corresponding physical noise is the projector onto $e\otimes\overline f$ for $p=e\otimes f$. If a quotient maximizer has unequal Schmidt coefficients, then $q_{\min}<0$ and $R_s=R_g=R_{\rm prod}=-1/q_{\min}$.
--   When the minimum is negative, a unit product vector realizes the stated least update weight.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 12, III.14 — Proposition III.14 (Inverse partial-transpose reduction). Let ρ be an entangled two-qubit state and put A = ρΓ . Let

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 12, Proposition III.14 (Inverse partial-transpose reduction). Let ρ be an entangled two-qubit state and put A = ρΓ . Let. -/
theorem inverseTransposeReduction (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) (he : ¬sep rho) :
  (pt rho).det≠0 ∧
  IsLeast {q : ℝ | ∃ p : Vec QQ, unitProduct p ∧ q=quad ((pt rho)⁻¹) p} (qmin ((pt rho)⁻¹)) ∧
  (∀ e f : Vec (Fin 2), ‖e‖=1 → ‖f‖=1 →
    pt (proj (tensor e f))=proj (tensor e (conjugate f)) ∧
      QAlgorithms.IsDensityMatrix (pt (proj (tensor e f))) ∧ sep (pt (proj (tensor e f)))) ∧
  (qmin ((pt rho)⁻¹)<0 →
    rprod rho=ENNReal.ofReal (-(qmin ((pt rho)⁻¹))⁻¹) ∧
    ∃ p : Vec QQ, unitProduct p ∧
      (pt rho+(-(qmin ((pt rho)⁻¹))⁻¹:ℂ) • proj p).PosSemidef) ∧
  (0≤qmin ((pt rho)⁻¹) → rprod rho=⊤ ∧
    ¬∃ (t : ℝ) (p : Vec QQ), 0≤t ∧ unitProduct p ∧ (pt rho+(t:ℂ) • proj p).PosSemidef) ∧
  ((∃ b : Vec QQ, maximizer rho b ∧ 1/2<schmidtSq b) →
    qmin ((pt rho)⁻¹)<0 ∧ rs rho=rg rho ∧
    rg rho=-(qmin ((pt rho)⁻¹))⁻¹ ∧ rprod rho=ENNReal.ofReal (rg rho)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
