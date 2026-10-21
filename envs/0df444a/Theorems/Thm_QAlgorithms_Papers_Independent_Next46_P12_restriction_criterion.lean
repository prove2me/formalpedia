-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_restriction_criterion
-- name    : QAlgorithms.Papers.Independent.Next46.P12.restriction_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:06:21.296328+00:00
-- url     : https://prove2.me/theorems/95d39fb1-426e-4786-9dab-f957abf67b7a
-- title:
--   Proposition 1.2: multiplicity-free restriction iff commutative centralizer
-- statement:
--   Let $B\hookrightarrow A$ be a unital injective homomorphism of finite-dimensional split semisimple algebras over a field $k$. For a simple $B$-module $U$ and a simple $A$-module $V$, the multiplicity of $U$ in $V|_B$ is $\dim_k\operatorname{Hom}_B(U,V|_B)$. Then
--
--   $$\bigl(\forall U,V,\ \dim_k\operatorname{Hom}_B(U,V|_B)\le1\bigr)\quad\Longleftrightarrow\quad Z(B,A)\text{ is commutative},$$
--
--   where $Z(B,A)=\{a\in A:ab=ba\text{ for all }b\in B\}$.
--
--   The criterion characterizes multiplicity-free restriction for a single adjacent inclusion.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 3, Proposition 1.2: multiplicity-free restriction iff commutative centralizer

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Proposition 1.2, source PDF p. 3. One adjacent unital inclusion suffices;
multiplicity-free restriction is not assumed before stating the equivalence. -/
theorem restriction_criterion {B : Type w} [Ring B] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B]
    (DB : SplitPresentation k B) (DA : SplitPresentation k A)
    (inc : B →ₐ[k] A) (hinj : Function.Injective inc) :
    MultiplicityFreeRestriction DB DA inc ↔
      ∀ x y : Subalgebra.centralizer k (Set.range inc), x * y = y * x := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
