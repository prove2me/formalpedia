-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_center_generator_criterion
-- name    : QAlgorithms.Papers.Independent.Next46.P12.center_generator_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:09:05.929386+00:00
-- url     : https://prove2.me/theorems/94bc0f85-03aa-4a2f-88fc-813980866ac9
-- title:
--   Lemma 2.1: center generators and simple spectrum
-- statement:
--   Let $A$ be a finite-dimensional split semisimple unital algebra over a field $k$. Choose a split presentation $A\cong\prod_{\lambda\in I}\operatorname{End}_k(V^\lambda)$, where the $V^\lambda$ are all its nonzero simple left modules, one per isomorphism class. Let $\epsilon(\lambda)$ be the inverse image of identity in block $\lambda$ and zero in the other blocks. For $z\in Z(A)$ write $a_\lambda$ for its scalar on $V^\lambda$, and let $\chi^\lambda(a)=\operatorname{tr}(a|_{V^\lambda})$. For every $z\in Z(A)$,
--
--   $$k[z]=Z(A)\quad\Longleftrightarrow\quad(\lambda\mapsto a_\lambda)\text{ is injective}.$$
--
--   If $k$ has at least $|I|$ elements, then some $z\in Z(A)$ generates $Z(A)$ as a $k$-algebra.
--
--   A simple spectrum exactly characterizes a center generator.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 8, Lemma 2.1: center generators and simple spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Lemma 2.1(a,b), source PDF p. 8. The cardinality condition includes finite
fields of sufficient size, expressed by embedding the full set of simple labels. -/
theorem center_generator_criterion [FiniteDimensional k A] (D : SplitPresentation k A) :
    (∀ z : Subalgebra.center k A,
      GeneratesCenter (k := k) (z : A) ↔ Function.Injective (centralSpectrum D (z : A))) ∧
    (Nonempty (D.Label ↪ k) →
      ∃ z : Subalgebra.center k A, GeneratesCenter (k := k) (z : A)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
