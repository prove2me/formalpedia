-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_unique_capacity_reconstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P62.unique_capacity_reconstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:43:56.728459+00:00
-- url     : https://prove2.me/theorems/713d822a-7e07-4a77-aa6f-d48115c21ba3
-- title:
--   Theorem 4.6: unique capacity reconstruction
-- statement:
--   Let $A$ be transmittable through $\Phi$ and suppose it simultaneously contains $c_d(\Phi)$ equal $d$-blocks for every $1\le d\le d_{\max}(\Phi)$. Then
--   $$N_d(\Phi)\ge0\quad(1\le d\le d_{\max}(\Phi)),\qquad A\cong A_{\rm cap}(\Phi).$$
--   Neither domination nor nonnegativity is assumed. This makes hybrid capacities determine the only possible simultaneous container.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 34, Theorem 4.6: unique capacity reconstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.34, 35, Theorem 4.6: unique capacity reconstruction. -/
theorem unique_capacity_reconstruction [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    (hpack : ∀ d ∈ Icc 1 (dmax F), Embeds (equalBlocks d (hybrid F d)) A) :
    (∀ d ∈ Icc 1 (dmax F), 0 ≤ multiplicity F d) ∧ capacityAlgebra F = some A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
