-- Prove2me | Theorems.Thm_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
-- name    : Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/86bd1fab-03a5-5175-ac7b-99ddd4b389ea
-- title:
--   Integrality of y⁻¹ from a monic symmetric bivariate relation
-- statement:
--   Let $R$ be a commutative ring, $A$ a field that is an $R$-algebra, $n$ a natural number, and $P \in R[X][Y]$ a polynomial in the outer variable $Y$ with coefficients in $R[X]$ which is monic of degree $n+1$ in $Y$ and symmetric in the sense that for all indices $i, j$ the $j$-th coefficient of $P.\mathrm{coeff}\,i$ equals the $i$-th coefficient of $P.\mathrm{coeff}\,j$, i.e. the coefficient of $X^jY^i$ equals that of $X^iY^j$. The assertion is that there exists a single polynomial $h \in R[X]$, depending only on these data and not on the elements below, such that for all $x, y, c \in A$ with $x \neq 0$ and $y \neq 0$, if $P$ evaluates to $0$ at $(x,y)$ — outer variable at $y$, inner variable at $x$ after transporting coefficients along $R \to A$ — and if $c$ is a multiplicative inverse of $1 + x^{-1}h(x^{-1})$, meaning $c\,(1 + x^{-1}\,h(x^{-1})) = 1$, then $y^{-1}$ is integral over the $R$-subalgebra $\mathrm{adjoin}_R\{x^{-1}, c\}$ of $A$, that is, $y^{-1}$ satisfies a monic polynomial with coefficients in that subalgebra.
--
--   This is the elementary reversal step for a symmetric monic bivariate relation: dividing $P(x,y)=0$ by $x^{n+1}y^{n+1}$ turns it into a relation for $y^{-1}$ over $R[x^{-1}]$ whose leading coefficient is $1 + x^{-1}h(x^{-1})$, so inverting that one element makes the relation monic. It is used in the treatment of the modular polynomial near the cusp, being cited by the lemmas on membership in the finite and infinite chart algebras of the modular curve and their compatibility with $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
    (R : Type*) [CommRing R] (A : Type*) [Field A] [Algebra R A]
    (n : ℕ) (P : Polynomial (Polynomial R)) (hmon : P.Monic) (hdeg : P.natDegree = n + 1)
    (hsym : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i) :
    ∃ h : Polynomial R,
      ∀ (x y c : A), x ≠ 0 → y ≠ 0 →
        P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y = 0 →
        c * (1 + x⁻¹ * Polynomial.aeval x⁻¹ h) = 1 →
        IsIntegral (Algebra.adjoin R ({x⁻¹, c} : Set A)) y⁻¹ := by sorry
