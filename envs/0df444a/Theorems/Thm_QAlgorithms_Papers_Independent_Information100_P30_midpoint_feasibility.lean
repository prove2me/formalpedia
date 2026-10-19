-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_midpoint_feasibility
-- name    : QAlgorithms.Papers.Independent.Information100.P30.midpoint_feasibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:22:30.106066+00:00
-- url     : https://prove2.me/theorems/6ef2ed30-146a-4a36-86e7-8b853d3ac8a9
-- title:
--   Qualitative midpoint feasibility
-- statement:
--   Let $\Lambda_1,\Lambda_2$ be arbitrary complex-linear CPTP qubit maps. If $\Lambda_2\circ\Lambda_1$ is not entanglement breaking, then
--
--   $$\Lambda_1\otimes\Lambda_2\notin\mathrm{EA},\qquad\exists\rho\succeq0,\ \operatorname{Tr}\rho=1:\ (\Lambda_1\otimes\Lambda_2)(\rho)\notin\mathrm{Sep}.$$
--
--   Here $\rho$ is a two-qubit density operator and $\mathrm{Sep}$ is the set of separable density operators. The witness may depend on both channels and need not match an endpoint witness. This is an existential feasibility statement, with no entanglement-measure comparison.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 4, Corollary 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Corollary 2 (PDF p.4, Eq.(44)): non-EB sequential transmission implies an
entangled density input survives the parallel action; the witness may depend on both channels. -/
theorem midpoint_feasibility (F G : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hG : IsQubitChannel G)
    (hnotEB : ¬ Entanglement.IsEntanglementBreaking (G.comp F)) :
    ¬ IsParallelEA F G ∧ ∃ rho : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      IsDensityMatrix rho ∧ ¬ Entanglement.IsSeparableDensity (tensorMap F G rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
