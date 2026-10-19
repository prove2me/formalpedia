-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_faithful_dimension
-- name    : QAlgorithms.Papers.Independent.Information100.P62.faithful_dimension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:31:36.684835+00:00
-- url     : https://prove2.me/theorems/e745b657-d352-4f24-937f-76e41f5fc8e4
-- title:
--   Lemma 2.2: faithful representation dimension
-- statement:
--   For a nonzero algebra $A=\bigoplus_k M_{d_k}(\mathbb C)$ with positive block sizes and positive integer $D$,
--   $$A\le M_D(\mathbb C)\iff\sum_k d_k\le D.$$
--   There are only finitely many isomorphism classes admitting faithful representation on $\mathbb C^D$. The dimension is the sum of block sizes, rather than the vector-space dimension of the algebra.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 12, Lemma 2.2: faithful representation dimension

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.12, Lemma 2.2: faithful representation dimension. -/
theorem faithful_dimension (A : Shape) (hA : Valid A) (D : ℕ) (hD : 0 < D) :
    (Embeds A (quantum D) ↔ lengthDim A ≤ D) ∧
    {B : Shape | Valid B ∧ Embeds B (quantum D)}.Finite := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
