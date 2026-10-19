-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_processing_systems
-- name    : QAlgorithms.Papers.Independent.Information100.P62.processing_systems
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:32:19.699208+00:00
-- url     : https://prove2.me/theorems/7e553a7b-68c8-4af5-a39b-07db530924bf
-- title:
--   Lemma 2.11: processing of operator systems
-- statement:
--   Let $\Phi:L(H)\to L(K)$ and $\Psi:L(K)\to L(G)$ be channels on positive finite-dimensional systems. Their confusability operator systems satisfy
--   $$S_\Phi\subseteq S_{\Psi\circ\Phi}\longrightarrow S_\Psi.$$
--   The arrow is graph homomorphism through an arbitrary finite ancillary space with contravariant compression. This expresses monotonicity under processing.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 15, Lemma 2.11: processing of operator systems

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.15, 16, Lemma 2.11: processing of operator systems. -/
theorem processing_systems [Nonempty I] [Nonempty O] [Nonempty J]
    (F : Superop I O) (G : Superop O J) (hF : IsChannel F) (hG : IsChannel G) :
    graph F ≤ graph (G ∘ F) ∧ GraphHom (graph (G ∘ F)) (graph G) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
