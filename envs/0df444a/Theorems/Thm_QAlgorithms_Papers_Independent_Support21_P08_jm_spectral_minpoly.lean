-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_jm_spectral_minpoly
-- name    : QAlgorithms.Papers.Independent.Support21.P08.jm_spectral_minpoly
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:28:27.072246+00:00
-- url     : https://prove2.me/theorems/6f34ae03-4dda-44a8-9f8f-b3b277834c1e
-- title:
--   Spectral expansions and exact JM minimal polynomials
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Let $\mathcal C(i)=\{c_t(i):t\in T(\Lambda)\}$ be the distinct contents at position $i$. Then
--
--   $$L_i=\sum_t c_t(i)F_t,\qquad\operatorname{minpoly}_K(L_i)=\prod_{c\in\mathcal C(i)}(X-c).$$
--
--   The second formula is a polynomial in $X$, not the zero algebra element obtained by evaluating it at $L_i$. Repeated contents contribute only one factor.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 14, 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

/-- Corollary 3.17, PDF p.14. The minimal polynomial has variable X;
the source's product of L_i-c is its evaluation, not a polynomial itself.
Uses complete content-sequence separation, correcting Definition 2.8. -/
theorem jm_spectral_minpoly (J : JMFamily D M) (hsep : separatesAll J) (i : Fin M) :
    J.L i = ∑ t : CellTableau Shape T, J.content t i • jmSpectralProjector J t ∧
    minpoly K (J.L i) = ∏ c ∈ contents J i, (Polynomial.X - Polynomial.C c) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
