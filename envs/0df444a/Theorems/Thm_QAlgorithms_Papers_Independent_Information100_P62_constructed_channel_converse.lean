-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_constructed_channel_converse
-- name    : QAlgorithms.Papers.Independent.Information100.P62.constructed_channel_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T22:00:51.042441+00:00
-- url     : https://prove2.me/theorems/74a797c9-bb95-4953-9e95-dcd0dc1b658e
-- title:
--   Lemma 5.8: converse charges for both constructed channels
-- statement:
--   For a nonzero type $A=\bigoplus_jM_{q_j}(\mathbb C)$ and $n\ge1$, the constructed channels satisfy the separate implications
--   $$A\in\mathcal T(\Phi^{\otimes n})\Rightarrow q_j\le2^n\ (\forall j),\ \sum_js_n(q_j)\le3^n,$$
--   $$A\in\mathcal T(\Psi^{\otimes n})\Rightarrow q_j\le2^n\ (\forall j),\ \sum_js_n(q_j)\le6^n.$$
--   Codes for $\Psi$ may have coherent support across different selector sectors. These charge converses establish maximality in Proposition 5.5.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 52, Lemma 5.8: converse charges for both constructed channels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.52, 53, Lemma 5.8: converse charges for both constructed channels. -/
theorem constructed_channel_converse (n : ℕ) (hn : 1 ≤ n) (A : Shape) (hA : Valid A) :
    (Transmits (tensorPower example43 n) A →
      (∀ q ∈ A, q ≤ 2 ^ n) ∧ (A.map (charge n)).sum ≤ 3 ^ n) ∧
    (Transmits (tensorPower selectorChannel n) A →
      (∀ q ∈ A, q ≤ 2 ^ n) ∧ (A.map (charge n)).sum ≤ 6 ^ n) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
