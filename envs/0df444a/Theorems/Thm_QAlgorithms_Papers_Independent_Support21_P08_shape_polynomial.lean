-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_shape_polynomial
-- name    : QAlgorithms.Papers.Independent.Support21.P08.shape_polynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:31:03.572992+00:00
-- url     : https://prove2.me/theorems/760ffc0a-85c8-4fd4-b90f-5ada89e14692
-- title:
--   Shape matrices satisfy the characteristic polynomial
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. If $Z$ has shape $J$ and $k=|J|$, then
--
--   $$(Z-I)^k Z^{d-k}=0.$$
--
--   When $k=1$, also $Z^d=Z^{d-1}$, $Z^{d+j}=Z^d$ for every $j\ge1$, and $F=Z^d$ is idempotent. Nonempty $J$ ensures $d\ge1$; idempotence is not claimed for arbitrary $k$.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 24, App.2-shape

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix §2, PDF p.24: shape-J characteristic polynomial, with the
singleton consequence F=Z^d. The idempotent conclusion is only for |J|=1. -/
theorem shape_polynomial [IsDomain R] {d : ℕ}
    (Z : Matrix (Fin d) (Fin d) R) (J : Finset (Fin d)) (hshape : HasShape Z J) :
    Polynomial.aeval Z
      ((Polynomial.X - 1) ^ J.card * Polynomial.X ^ (d - J.card) : Polynomial R) = 0 ∧
    (J.card = 1 →
      Z ^ d = Z ^ (d - 1) ∧ (∀ j : ℕ, 1 ≤ j → Z ^ (d + j) = Z ^ d) ∧
      (Z ^ d) * (Z ^ d) = Z ^ d) := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
