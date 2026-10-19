-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_negativityBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P21.negativityBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:57:41.088597+00:00
-- url     : https://prove2.me/theorems/a51e7f4c-9ef6-455f-8a19-a1be7c7d0957
-- title:
--   VII.19 — Proposition VII.19 (Negativity bounds and equality condition). For every entangled two-qubit state,
-- statement:
--   For an entangled two-qubit state, let $\mathcal N=(\|\rho^\Gamma\|_1-1)/2$, let $v_-$ be its unit negative eigenvector, $C_-$ its pure concurrence, and $C(\rho)$ the mixed-state concurrence. Then
--   $$\frac{2\mathcal N}{1+\sqrt{1-C_-^2}}\le R_s(\rho)=R_g(\rho)\le2\mathcal N\le C(\rho),\qquad\mathcal N<R_s(\rho).$$
--   Moreover, $R_s(\rho)=2\mathcal N$ exactly when $v_-$ is maximally entangled. The negative direction is unique up to phase; the statement applies to every normalized choice of it. The comparison $2\mathcal N\le C$ is credited to Ref. [39].
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 23, VII.19 — Proposition VII.19 (Negativity bounds and equality condition). For every entangled two-qubit state,

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 23, Proposition VII.19 (Negativity bounds and equality condition). For every entangled two-qubit state,. -/
theorem negativityBounds (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) (he : ¬sep rho) :
  0<QAlgorithms.Entanglement.negativity rho ∧
  (∃ v : Vec QQ, ‖v‖=1 ∧ (pt rho).mulVec (fun i => v i)=(-QAlgorithms.Entanglement.negativity rho:ℂ) • (fun i => v i)) ∧
  ∀ v : Vec QQ, ‖v‖=1 → (pt rho).mulVec (fun i => v i)=(-QAlgorithms.Entanglement.negativity rho:ℂ) • (fun i => v i) →
    2*QAlgorithms.Entanglement.negativity rho/(1+Real.sqrt (1-pureConcurrence v^2)) ≤ rs rho ∧
    rs rho≤2*QAlgorithms.Entanglement.negativity rho ∧ 2*QAlgorithms.Entanglement.negativity rho≤concurrence rho ∧
    QAlgorithms.Entanglement.negativity rho<rs rho ∧ (rs rho=2*QAlgorithms.Entanglement.negativity rho ↔ schmidtSq v=1/2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
