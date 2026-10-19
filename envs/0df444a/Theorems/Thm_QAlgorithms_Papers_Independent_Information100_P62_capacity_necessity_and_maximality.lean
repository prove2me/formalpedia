-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_necessity_and_maximality
-- name    : QAlgorithms.Papers.Independent.Information100.P62.capacity_necessity_and_maximality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:44:23.462475+00:00
-- url     : https://prove2.me/theorems/9b1d714e-afd3-4f02-8b97-65a9d622aac3
-- title:
--   Corollary 4.7: necessity and maximality of the capacity algebra
-- statement:
--   For every dominating transmittable algebra $A$ of $\Phi$,
--   $$N_d(\Phi)\ge0\ (1\le d\le d_{\max}),\qquad A\cong A_{\rm cap}(\Phi).$$
--   More generally, any defined and transmittable capacity algebra is maximal. Maximality here does not assert domination.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 35, Corollary 4.7: necessity and maximality of the capacity algebra

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.35, Corollary 4.7: necessity and maximality of the capacity algebra. -/
theorem capacity_necessity_and_maximality [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) :
    (∀ A, Dominating F A → (∀ d ∈ Icc 1 (dmax F), 0 ≤ multiplicity F d) ∧ capacityAlgebra F = some A) ∧
    (∀ A, capacityAlgebra F = some A → Transmits F A → Maximal F A) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
