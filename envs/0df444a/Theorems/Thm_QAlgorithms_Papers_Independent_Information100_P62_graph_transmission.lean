-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_graph_transmission
-- name    : QAlgorithms.Papers.Independent.Information100.P62.graph_transmission
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:36:58.351192+00:00
-- url     : https://prove2.me/theorems/d054ebd6-ef9d-4329-b437-6366a718acb2
-- title:
--   Lemma 3.6: transmission under graph homomorphism
-- statement:
--   For channels $\Phi,\Psi$ on positive finite-dimensional systems,
--   $$S_\Phi\to S_\Psi\quad\Longrightarrow\quad\mathcal T(\Phi)\subseteq\mathcal T(\Psi).$$
--   Every algebra transmitted by the first channel is transmitted by the second.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 24, Lemma 3.6: transmission under graph homomorphism

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.24, Lemma 3.6: transmission under graph homomorphism. -/
theorem graph_transmission [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (F : Superop I O) (G : Superop J K) (hF : IsChannel F) (hG : IsChannel G)
    (h : GraphHom (graph F) (graph G)) (A : Shape) (hA : Transmits F A) : Transmits G A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
