-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_embedding_packing
-- name    : QAlgorithms.Papers.Independent.Information100.P62.embedding_packing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:30:59.434968+00:00
-- url     : https://prove2.me/theorems/7b6e4e68-cee4-49e3-bc16-434ce399f9ab
-- title:
--   Unnumbered embedding/packing equivalence (2.8)
-- statement:
--   Let $A=\bigoplus_k M_{d_k}(\mathbb C)$ and $B=\bigoplus_l M_{n_l}(\mathbb C)$ be nonzero finite-dimensional algebras with positive block sizes. Nonunital faithful complex-linear star-embedding is equivalent to
--   $$A\le B\iff\exists f,\quad\sum_{k:f(k)=l}d_k\le n_l\quad\text{for every }l.$$
--   It is also equivalent to a nonnegative integer matrix $\Lambda$ with $\sum_k\Lambda_{kl}d_k\le n_l$ and $\sum_l\Lambda_{kl}\ge1$. This identifies the embedding order with packing.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 11, Unnumbered embedding/packing equivalence (2.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.11, 12, Unnumbered embedding/packing equivalence (2.8). -/
theorem embedding_packing (A B : Shape) (hA : Valid A) (hB : Valid B) :
    (Embeds A B ↔ Packs A B) ∧ (Embeds A B ↔ MultiplicityPacking A B) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
