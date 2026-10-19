-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_finite_domination_criterion
-- name    : QAlgorithms.Papers.Independent.Information100.P62.finite_domination_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:46:10.121889+00:00
-- url     : https://prove2.me/theorems/6f77aef5-6f71-4292-877c-2126be30bff8
-- title:
--   Theorem 4.11: exact finite domination criterion
-- statement:
--   For a channel $\Phi$ and a nonzero finite-dimensional algebra type $A$,
--   $$A\text{ dominates }\mathcal T(\Phi)\iff A\in\mathcal T(\Phi)\ \text{and}\ F(A)\cap\mathcal T(\Phi)=\varnothing.$$
--   The left side includes transmittability and existence of the proposed dominating type. This is an exact finite characterization.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 37, Theorem 4.11: exact finite domination criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.37, Theorem 4.11: exact finite domination criterion. -/
theorem finite_domination_criterion [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Dominating F A ↔ Transmits F A ∧ forbidden A ∩ transmission F = ∅ := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
