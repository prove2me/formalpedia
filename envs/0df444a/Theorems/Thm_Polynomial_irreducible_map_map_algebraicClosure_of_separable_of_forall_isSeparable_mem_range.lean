-- Prove2me | Theorems.Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
-- name    : Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ee4ca7a6-e4d8-54fb-8b92-5c2ed36f4156
-- title:
--   Absolute irreducibility of F under separable closedness in L
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and suppose that $K$ is separably closed in $L$: every $\theta \in L$ that is separable over $K$ lies in the image of the structure map $K \to L$. Let $d$ be a natural number, let $x : \mathrm{Fin}\,d \to L$ be a family of elements of $L$ that is algebraically independent over $K$, and let $y \in L$. Let $F$ be a polynomial in one variable over the polynomial ring $K[X_1,\dots,X_d]$ (i.e. $F \in \mathrm{MvPolynomial}(\mathrm{Fin}\,d,K)[T]$) which is monic, and assume that the image of $F$ in $T$ over the fraction field of $K[X_1,\dots,X_d]$, that is over $K(X_1,\dots,X_d)$, is both irreducible and separable. Assume finally that $F$ has the root $y$ after the coefficients are specialised through the $K$-algebra map $K[X_1,\dots,X_d] \to L$ sending $X_i \mapsto x_i$, i.e. $F(x_1,\dots,x_d;y)=0$. The conclusion is that the polynomial obtained from $F$ by applying $\mathrm{MvPolynomial.map}$ of the structure map $K \to \overline{K}$ to each coefficient is irreducible in $\overline{K}[X_1,\dots,X_d][T]$, where $\overline{K}$ is the algebraic closure `AlgebraicClosure K`.
--
--   This is the statement that such an $F$ is absolutely irreducible: irreducibility over $K(X_1,\dots,X_d)$ is preserved after base change to the algebraic closure of $K$, the input being that $K$ is separably closed in a field $L$ containing a generic point $(x,y)$ of the hypersurface $F=0$. The proof goes through the primality of the nilradical of $L \otimes_K \Omega$ for $\Omega/K$ algebraic, as recorded in [`Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range`](thm.html#Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range), and the result feeds into [`Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable`](thm.html#Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range)
    {d : ℕ} (x : Fin d → L) (hx : AlgebraicIndependent K x) (y : L)
    (F : Polynomial (MvPolynomial (Fin d) K)) (hFm : F.Monic)
    (hFirr : Irreducible (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))))
    (hFsep : (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))).Separable)
    (hroot : F.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom y = 0) :
    Irreducible (F.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) := by sorry
