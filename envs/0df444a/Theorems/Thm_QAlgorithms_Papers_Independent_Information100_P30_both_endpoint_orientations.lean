-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_both_endpoint_orientations
-- name    : QAlgorithms.Papers.Independent.Information100.P30.both_endpoint_orientations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:23:09.37299+00:00
-- url     : https://prove2.me/theorems/d27af7e5-b15b-445a-a7f5-f6169d7faee1
-- title:
--   Both endpoint orientations
-- statement:
--   Let $\Lambda_1,\Lambda_2$ be arbitrary complex-linear CPTP qubit maps. If their parallel action is entanglement annihilating on the positive cone, then
--
--   $$\Lambda_2\circ\Lambda_1\in\mathrm{EB}\quad\text{and}\quad\Lambda_1\circ\Lambda_2\in\mathrm{EB}.$$
--
--   Each EB conclusion quantifies over all density inputs and every finite-dimensional reference. Equivalently, existence of surviving entanglement at either endpoint implies existence of surviving entanglement at the midpoint, without a same-input guarantee.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 4, Corollary 3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Corollary 3 (PDF p.4, Eq.(45)): parallel EA forces both endpoint orders to be EB.
The equivalent existential feasibility reading makes no same-input claim. -/
theorem both_endpoint_orientations (F G : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hG : IsQubitChannel G) (hEA : IsParallelEA F G) :
    Entanglement.IsEntanglementBreaking (G.comp F) ∧
      Entanglement.IsEntanglementBreaking (F.comp G) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
