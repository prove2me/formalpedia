-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_product_lower_sets
-- name    : QAlgorithms.Papers.Independent.Information100.P62.product_lower_sets
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:54:57.973767+00:00
-- url     : https://prove2.me/theorems/5698e0a5-2c86-49ca-b670-46cc4ecf78e0
-- title:
--   Unnumbered product coding and principal product lower set (5.3)–(5.4)
-- statement:
--   Product coding transmits $A\otimes B$ through $\Phi\otimes\Psi$ whenever $A\in\mathcal T(\Phi)$ and $B\in\mathcal T(\Psi)$. With $I\star J$ the downward closure of products,
--   $$\mathcal T(\Phi)\star\mathcal T(\Psi)\subseteq\mathcal T(\Phi\otimes\Psi).$$
--   If $A,B$ respectively dominate the two transmission sets, then $\mathcal T(\Phi)\star\mathcal T(\Psi)=\{C:C\le A\otimes B\}$. Joint coding remains unrestricted.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 44, Unnumbered product coding and principal product lower set (5.3)–(5.4)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.44, Unnumbered product coding and principal product lower set (5.3)–(5.4). -/
theorem product_lower_sets [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (F : Superop I O) (G : Superop J K) (hF : IsChannel F) (hG : IsChannel G) :
    (∀ A B, Transmits F A → Transmits G B → Transmits (tensorChannel F G) (tensorShape A B)) ∧
    starLower (transmission F) (transmission G) ⊆ transmission (tensorChannel F G) ∧
    (∀ A B, Dominating F A → Dominating G B →
      starLower (transmission F) (transmission G) = {C | Valid C ∧ Embeds C (tensorShape A B)}) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
