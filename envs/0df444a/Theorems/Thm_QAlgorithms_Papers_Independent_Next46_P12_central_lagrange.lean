-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_central_lagrange
-- name    : QAlgorithms.Papers.Independent.Next46.P12.central_lagrange
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:10:16.914918+00:00
-- url     : https://prove2.me/theorems/d569bfce-1764-4a55-b8d0-415ee94a50d0
-- title:
--   Proposition 2.3: central Lagrange interpolation
-- statement:
--   Let $A$ be a finite-dimensional split semisimple unital algebra over a field $k$. Choose a split presentation $A\cong\prod_{\lambda\in I}\operatorname{End}_k(V^\lambda)$, where the $V^\lambda$ are all its nonzero simple left modules, one per isomorphism class. Let $\epsilon(\lambda)$ be the inverse image of identity in block $\lambda$ and zero in the other blocks. For $z\in Z(A)$ write $a_\lambda$ for its scalar on $V^\lambda$, and let $\chi^\lambda(a)=\operatorname{tr}(a|_{V^\lambda})$. If $z\in Z(A)$ generates the center, then for each $\lambda\in I$ every denominator below is nonzero, and
--
--   $$\epsilon(\lambda)=\prod_{\mu\in I,\ \mu\ne\lambda}\frac{z-a_\mu}{a_\lambda-a_\mu}.$$
--
--   The inverse denominators are scalars in $k$; the product is evaluated from a polynomial over $k$.
--
--   This recovers the primitive central projectors from one center generator and its scalar spectrum.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 8, Proposition 2.3: central Lagrange interpolation

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Proposition 2.3, source PDF pp. 8–9. Denominator nonvanishing is concluded,
not assumed. For one block the interpolation polynomial is the empty product 1. -/
theorem central_lagrange [FiniteDimensional k A] (D : SplitPresentation k A)
    (z : Subalgebra.center k A) (hz : GeneratesCenter (k := k) (z : A)) (i : D.Label) :
    (∀ j : D.Label, j ≠ i → centralSpectrum D (z : A) i - centralSpectrum D (z : A) j ≠ 0) ∧
    Polynomial.aeval (z : A) (centralPolynomial D (z : A) i) = centralIdempotent D i := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
