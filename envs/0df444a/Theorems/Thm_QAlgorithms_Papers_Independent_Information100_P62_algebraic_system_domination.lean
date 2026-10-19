-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_algebraic_system_domination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.algebraic_system_domination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:49:03.371632+00:00
-- url     : https://prove2.me/theorems/1adb6fac-7ec1-46dc-b6b7-61c43b332069
-- title:
--   Theorem 4.15: algebraic confusability system
-- statement:
--   If the confusability operator system $S_\Phi\subseteq L(H)$ of a channel is an ambient-unital star-subalgebra, then
--   $$\Phi\text{ has dominating algebra }A_{\rm dom}(\Phi)\cong S_\Phi'.$$
--   The commutant is taken in $L(H)$. Ambient algebra closure, rather than commutativity alone, is the hypothesis.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 39, Theorem 4.15: algebraic confusability system

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.39, 40, 57, 58, Theorem 4.15: algebraic confusability system. -/
theorem algebraic_system_domination [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (hS : IsAlgebra (graph F)) :
    ∃ A, HasType (commutant (graph F)) A ∧ Dominating F A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
