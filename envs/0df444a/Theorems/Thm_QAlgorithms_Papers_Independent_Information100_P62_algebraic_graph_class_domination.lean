-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_algebraic_graph_class_domination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.algebraic_graph_class_domination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:49:34.688555+00:00
-- url     : https://prove2.me/theorems/99010d05-0a7f-4261-81c1-4ff12b6f0d18
-- title:
--   Corollary 4.16: algebraic graph-equivalence class
-- statement:
--   Let $S_\Phi$ be graph-isomorphic to an ambient-unital star-subalgebra $S\subseteq L(H')$ on any positive finite-dimensional space. Then
--   $$\Phi\text{ has dominating algebra }A_{\rm dom}(\Phi)\cong S'.$$
--   The commutant is in $L(H')$, and graph equivalence allows arbitrary finite ancillary systems.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 40, Corollary 4.16: algebraic graph-equivalence class

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.40, Corollary 4.16: algebraic graph-equivalence class. -/
theorem algebraic_graph_class_domination [Nonempty I] [Nonempty O] [Nonempty J]
    (F : Superop I O) (hF : IsChannel F) (S : Submodule ℂ (Matrix J J ℂ))
    (hS : IsAlgebra S) (hiso : GraphIso (graph F) S) :
    ∃ A, HasType (commutant S) A ∧ Dominating F A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
