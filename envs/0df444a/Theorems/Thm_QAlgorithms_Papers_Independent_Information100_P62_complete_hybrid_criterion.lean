-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_complete_hybrid_criterion
-- name    : QAlgorithms.Papers.Independent.Information100.P62.complete_hybrid_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:46:51.522979+00:00
-- url     : https://prove2.me/theorems/5930b577-0c85-41b2-88ba-e8a9264879f0
-- title:
--   Corollary 4.12: complete hybrid-capacity criterion
-- statement:
--   A channel $\Phi$ has a dominating transmittable algebra exactly when all three conditions hold:
--   $$N_d(\Phi)\ge0\ (1\le d\le d_{\max}),\qquad A_{\rm cap}\in\mathcal T(\Phi),\qquad F(A_{\rm cap})\cap\mathcal T(\Phi)=\varnothing.$$
--   The first condition defines the capacity algebra; the latter two test its transmission and its forbidden types. When they hold, $A_{\rm cap}$ itself dominates.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 37, Corollary 4.12: complete hybrid-capacity criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.37, 38, Corollary 4.12: complete hybrid-capacity criterion. -/
theorem complete_hybrid_criterion [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) :
    (HasDominating F ↔ (∀ d ∈ Icc 1 (dmax F), 0 ≤ multiplicity F d) ∧
      ∃ A, capacityAlgebra F = some A ∧ Transmits F A ∧ forbidden A ∩ transmission F = ∅) ∧
    (∀ A, capacityAlgebra F = some A → Transmits F A →
      forbidden A ∩ transmission F = ∅ → Dominating F A) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
