-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_algebra_need_not_dominate
-- name    : QAlgorithms.Papers.Independent.Information100.P62.capacity_algebra_need_not_dominate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:45:10.209045+00:00
-- url     : https://prove2.me/theorems/141bd413-d04b-43f4-a53b-588883def0b7
-- title:
--   Remark 4.8: a transmittable capacity algebra need not dominate
-- statement:
--   For the channel on $M_6(\mathbb C)$ with $E_0=\sum_{j=0}^3|j\rangle\langle j|$ and $E_1=|3\rangle\langle4|+|4\rangle\langle5|$, both $M_4\oplus\mathbb C$ and $M_3\oplus M_2$ are transmittable. Its data are
--   $$d_{\max}=4,\quad(c_1,c_2,c_3,c_4)=(5,2,1,1),\quad(N_1,N_2,N_3,N_4)=(1,0,0,1).$$
--   Thus $A_{\rm cap}=M_4\oplus\mathbb C$ is defined and transmittable, but $M_3\oplus M_2$ does not embed in it and no dominating algebra exists. This disproves the reverse implication in Corollary 4.7.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 35, Remark 4.8: a transmittable capacity algebra need not dominate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.35, 36, Remark 4.8: a transmittable capacity algebra need not dominate. -/
theorem capacity_algebra_need_not_dominate :
    IsChannel capacityExample ∧
    Transmits capacityExample (quantum 4 + quantum 1) ∧
    Transmits capacityExample (quantum 3 + quantum 2) ∧ dmax capacityExample = 4 ∧
    hybrid capacityExample 1 = 5 ∧ hybrid capacityExample 2 = 2 ∧
    hybrid capacityExample 3 = 1 ∧ hybrid capacityExample 4 = 1 ∧
    multiplicity capacityExample 1 = 1 ∧ multiplicity capacityExample 2 = 0 ∧
    multiplicity capacityExample 3 = 0 ∧ multiplicity capacityExample 4 = 1 ∧
    capacityAlgebra capacityExample = some (quantum 4 + quantum 1) ∧
    ¬ Embeds (quantum 3 + quantum 2) (quantum 4 + quantum 1) ∧ ¬ HasDominating capacityExample := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
