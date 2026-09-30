-- Prove2me | Theorems.Thm_TranscendenceTheory_bivariate_resultant_cyclic_dimension_bound
-- name    : TranscendenceTheory.bivariate_resultant_cyclic_dimension_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T15:07:33.771505+00:00
-- url     : https://prove2.me/theorems/d4602f39-33ea-40db-b290-ac366ca6ba71
-- title:
--   Cyclic dimension bound from two bivariate relations and their resultant
-- statement:
--   Let $A$ be any commutative complex algebra and let $x,y\in A$. Let $F,H\in\mathbb C[X][Y]$, and let $a,b\in\mathbb N$ bound the $X$-degrees of every coefficient of $F,H$, respectively. Suppose at least one of $F,H$ has positive $Y$-degree, their resultant $R(X)=\operatorname{Res}_Y(F,H)$ is a nonzero polynomial, and
--   $$F(x,y)=H(x,y)=0\quad\text{in }A.$$
--   Then $x$ is integral over $\mathbb C$ and
--   $$\dim_{\mathbb C}\mathbb C[x]\le (\deg_Y F)b+(\deg_Y H)a.$$
--
--   No finite-dimensionality or reducedness assumption is imposed on $A$. Polynomial degrees are Lean's natural degrees, which assign zero to the zero polynomial. Excluding the case where both $Y$-degrees are zero is necessary: Mathlib defines the corresponding empty Sylvester determinant to be one, and it need not give a Bezout relation in that case.
-- source:
--   Derived elimination step for https://prove2.me/theorems/2301083d-8664-4f21-b709-ebed43665718. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a general resultant bound applied to the already formalized contact quotient, not a claimed proof of the paper zero estimate. Primary Lean sources: Mathlib RingTheory/Polynomial/Resultant/Basic.lean (Sylvester determinant and Bezout identity), Algebra/Polynomial/BigOperators.lean (degrees of sums and products), RingTheory/Algebraic/Integral.lean, and RingTheory/Adjoin/PowerBasis.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining construction asks for two relations with nonzero resultant and bounded elimination cost. It is equivalent to the selected rank estimate with the same uniform constant.

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Polynomial
open scoped Classical

theorem TranscendenceTheory.bivariate_resultant_cyclic_dimension_bound
    (A : Type*) [CommRing A] [Algebra ℂ A] (x y : A)
    (F H : Polynomial (Polynomial ℂ)) (a b : ℕ)
    (hF : ∀ i, (F.coeff i).natDegree ≤ a)
    (hH : ∀ i, (H.coeff i).natDegree ≤ b)
    (hdegree : F.natDegree ≠ 0 ∨ H.natDegree ≠ 0)
    (hres : F.resultant H ≠ 0)
    (hFx : F.eval₂ (Polynomial.aeval x).toRingHom y = 0)
    (hHx : H.eval₂ (Polynomial.aeval x).toRingHom y = 0) :
    IsIntegral ℂ x ∧
      Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set A)) ≤
        F.natDegree * b + H.natDegree * a := by sorry
