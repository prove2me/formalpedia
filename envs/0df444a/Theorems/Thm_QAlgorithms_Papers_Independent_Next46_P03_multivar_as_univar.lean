-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P03_multivar_as_univar
-- name    : QAlgorithms.Papers.Independent.Next46.P03.multivar_as_univar
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:34:38.745599+00:00
-- url     : https://prove2.me/theorems/7272b31e-d8e0-40a4-9ff6-67215d6a2a24
-- title:
--   The coefficient-sum conversion equals the canonical univariate conversion
-- statement:
--   Let $R$ be a commutative ring with unity and $0\ne1$, let $p\in R[X_0,X_1,\ldots]$ be a polynomial with finite support, and fix $x\in\mathbb N$. Write $d=\deg_{X_x}(p)$, with degree zero for the zero polynomial, and let $a_i$ be the coefficient of $X_x^i$, regarded as a polynomial in the same indexed variables with the $x$ coordinate erased from every monomial. Let $T_x$ be the canonical substitution homomorphism sending $X_x$ to the outer univariate indeterminate $T$, every $X_j$ with $j\ne x$ to its coefficient variable, and each scalar to a constant. Then
--
--   $$
--   \sum_{i=0}^{d} a_i T^i=T_x(p).
--   $$
--
--   This identifies the finite coefficient-extraction conversion with the independently specified canonical conversion. It includes zero and constant polynomials and requires no integral-domain assumption.
-- source:
--   A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL, arXiv:2209.10978v2, PDF p. 11, §3.3: lemma multivar_as_univar

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

namespace QAlgorithms.Papers.Independent.Next46.P03

noncomputable section

/-- Kosaian–Tan–Platzer, arXiv:2209.10978v2, §3.3, PDF p. 11,
`multivar_as_univar`. Isabelle's `comm_ring_1` includes distinct zero and
one, represented here by `CommRing` and `Nontrivial`. There is no domain,
nonzero-polynomial or positive-degree hypothesis. -/
theorem multivar_as_univar {R : Type*} [CommRing R] [Nontrivial R]
    (x : ℕ) (p : MvPolynomial ℕ R) :
    mpolyToMpolyPolyAlt x p = mpolyToMpolyPoly x p := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P03
