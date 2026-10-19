-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_graph_invariant
-- name    : QAlgorithms.Papers.Independent.Information100.P62.graph_invariant
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:37:42.503239+00:00
-- url     : https://prove2.me/theorems/c1681255-44d8-4e1a-814e-8efe2bcc8b87
-- title:
--   Corollary 3.7: transmission is a graph invariant
-- statement:
--   If the operator systems of channels $\Phi$ and $\Psi$ are mutually graph homomorphic, then
--   $$\mathcal T(\Phi)=\mathcal T(\Psi).$$
--   The equality concerns algebra isomorphism types, and does not require a spatial isomorphism of the systems.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 24, Corollary 3.7: transmission is a graph invariant

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.24, Corollary 3.7: transmission is a graph invariant. -/
theorem graph_invariant [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (F : Superop I O) (G : Superop J K) (hF : IsChannel F) (hG : IsChannel G)
    (h : GraphIso (graph F) (graph G)) : transmission F = transmission G := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
