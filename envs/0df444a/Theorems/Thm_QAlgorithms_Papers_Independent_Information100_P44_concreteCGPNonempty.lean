-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_concreteCGPNonempty
-- name    : QAlgorithms.Papers.Independent.Information100.P44.concreteCGPNonempty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:47:03.911219+00:00
-- url     : https://prove2.me/theorems/1ad066a2-3b6a-470a-82f1-61961abf9ceb
-- title:
--   Remark 7: fixed CGP feasible set is nonempty
-- statement:
--   For $H=\operatorname{diag}(0,1,1,3)$, $\beta=1$, input state of Eq. (111), and coarse target populations $(1/2,7/20,3/20)$,
--   $$\Gamma_{\rm CGP}(\rho,p^f)\ne\varnothing.$$
--   Equivalently there is an output-first Choi matrix satisfying all the concrete SDP constraints. This asserts CGP feasibility without treating rounded thermomajorization coordinates as exact witnesses or asserting finite-bath thermal feasibility.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 17, Remark 7: fixed CGP feasible set is nonempty

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.17, Remark 7: existence in CGP is a conclusion, without a finite-TO witness claim. -/
theorem concreteCGPNonempty :
    (∃ Phi : Map 4, FixedChannelFeasible Phi) ∧
    ∃ J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ, FixedChoiFeasible J := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
