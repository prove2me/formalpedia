-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_theorem_3_8
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.theorem_3_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:59:00.697974+00:00
-- url     : https://prove2.me/theorems/399cfe43-e6f6-4bb6-a825-27bffad6b6ba
-- title:
--   Generic semisimplicity and the specified 3r-squared basis
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   Let $R=\mathbb Q(u_1,\ldots,u_r,q)$ with the displayed generators algebraically independent. Put $U=\prod_i u_i$, $\gamma_r(z)=1$ for odd $r$ and $\gamma_r(z)=-z$ for even $r$, and define
--   $$\Gamma_i=\left(\gamma_r(u_i)+\delta^{-1}\rho(u_i^2-1)\prod_{j\ne i}u_j\right)\prod_{j\ne i}\frac{u_iu_j-1}{u_i-u_j}.$$
--   The rho choice means $\rho^{-1}\in\{U,-U\}$ for odd $r$, and $\rho^{-1}\in\{q^{-1}U,-qU\}$ for even $r$. Assume that every integer moment is $\omega_a=\sum_i u_i^a\Gamma_i$. Then $B_{r,2}$ is semisimple and the following indexed family is an $R$-basis:
--   $$\{X_1^\alpha X_2^\beta,\ X_1^\alpha X_2^\beta T_1,\ X_1^\alpha E_1X_1^\beta:0\le\alpha,\beta<r\}.$$
--
--   The basis has three blocks of $r^2$ vectors. Both semisimplicity and this particular basis, rather than existence of an unspecified basis, are asserted.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 9, Theorem 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section GenericTwoStrand

variable {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ}

/-- Theorem 3.8, PDF p.9: simultaneous semisimplicity and the explicit
indexed monomial basis, for all d=r parameter formulas and both rho choices. -/
theorem theorem_3_8 (P : Ground K r) (hK : IsGenericField P.toRuiXuUnitParameters)
    (hrho : RhoChoice P.toRuiXuUnitParameters)
    (homega : ∀ a : ℤ, P.omega a = spectralMoment (K := K) P.toRuiXuUnitParameters a) :
    IsSemisimpleModule (RuiXuBMW P 2) (RuiXuBMW P 2) ∧
      ∃ b : Module.Basis (Fin 3 × Fin r × Fin r) K (RuiXuBMW P 2),
        ∀ i, b i = twoStrandMonomial P i := by sorry

end GenericTwoStrand

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
