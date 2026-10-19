-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_quantum_capacity_criterion
-- name    : QAlgorithms.Papers.Independent.Information100.P62.small_quantum_capacity_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:48:30.625809+00:00
-- url     : https://prove2.me/theorems/f9518b61-c13d-494f-8e1d-286cd82cf100
-- title:
--   Corollary 4.14: domination criterion when dmax<=3
-- statement:
--   For a channel $\Phi$ with $d_{\max}(\Phi)\le3$,
--   $$\Phi\text{ has a dominating transmittable algebra}\iff A_{\rm cap}(\Phi)\text{ is defined and transmittable}.$$
--   In this regime the forbidden-type condition follows from the equal-block packing counts.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 39, Corollary 4.14: domination criterion when dmax<=3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.39, Corollary 4.14: domination criterion when dmax<=3. -/
theorem small_quantum_capacity_criterion [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (hsmall : dmax F ≤ 3) :
    HasDominating F ↔ ∃ A, capacityAlgebra F = some A ∧ Transmits F A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
