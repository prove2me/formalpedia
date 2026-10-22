-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_newton_cellular
-- name    : QAlgorithms.Papers.Independent.Support21.P08.newton_cellular
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:22:51.221837+00:00
-- url     : https://prove2.me/theorems/3a454140-b67c-4c0f-8c1d-6efced2cdd49
-- title:
--   The Newton quotient example is cellular with one JM element
-- statement:
--   Let $R$ be a commutative integral domain, $n\ge1$, and $c_1,\ldots,c_n\in R$. Set $A=R[X]/\prod_{j=1}^n(X-c_j)$ and let $x$ be the canonical image of $X$. Define $a_i=\prod_{j<i}(x-c_j)$ for $1\le i\le n+1$. The vectors $a_1,\ldots,a_n$ form the cellular basis with singleton cells, $a_{n+1}=0$, and $x$ is a JM element with content $c_i$ because
--
--   $$a_i x=c_i a_i+a_{i+1}\qquad(1\le i\le n).$$
--
--   This family separates precisely when the $c_i$ are pairwise distinct. The quotient and basis are computed, including their boundary value.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 6, 2.14

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section NewtonExample

variable {R : Type*} [CommRing R] [newtonDomain : IsDomain R]

include newtonDomain in
/-- Example 2.14, PDF p.6: literal Newton cellular basis, the boundary
vector, triangular action a_i x=c_i a_i+a_{i+1}, and exact separation iff
contents are pairwise distinct. The singleton-tableau cell datum is a conclusion. -/
theorem newton_cellular {n : ℕ} (hn : 1 ≤ n) (c : Fin n → R) :
    newtonVector c n = 0 ∧
    (∀ i : Fin n, newtonVector c i.val * AdjoinRoot.root (newtonPolynomial c) =
      c i • newtonVector c i.val + newtonVector c (i.val + 1)) ∧
    ∃ D : CellDatum (R := R) (A := NewtonAlgebra c) (T := fun _ : Fin n => Unit),
      (∀ i : Fin n, D.basis ⟨i, ((), ())⟩ = newtonVector c i.val) ∧
      ∃ J : JMFamily D 1,
        (∀ i, J.L i = AdjoinRoot.root (newtonPolynomial c)) ∧
        (∀ t i, J.content t i = c t.1) ∧
        (separatesComparable J ↔ Function.Injective c) := by sorry

end NewtonExample

end QAlgorithms.Papers.Independent.Support21.P08

end
