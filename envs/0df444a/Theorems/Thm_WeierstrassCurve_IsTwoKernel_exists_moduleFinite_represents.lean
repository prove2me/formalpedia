-- Prove2me | Theorems.Thm_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents
-- name    : WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/b82835b6-172e-5cf9-b00a-3ff0dd510b08
-- title:
--   A module-finite algebra representing monic linear divisors of Ψ₂²
-- statement:
--   Let $B$ be a commutative ring and $W$ a Weierstrass curve over $B$, and assume the image of $2$ in $B$ is a unit. Here a polynomial $h \in T[X]$ is said to be a two-kernel for a Weierstrass curve over a commutative ring $T$ when $\deg h \le 1$ (in the sense of `natDegree`), the coefficient of $X$ in $h$ is $1$, and $h$ divides the curve's polynomial $\Psi_2^2 = 4X^3 + b_2X^2 + 2b_4X + b_6$; that is, $h$ is a monic linear divisor of $\Psi_2^2$. The assertion is that there exist a commutative ring $C$ equipped with a $B$-algebra structure making it finite as a $B$-module, and a polynomial $h_u \in C[X]$ which is a two-kernel for the base change of $W$ along $B \to C$, such that for every commutative ring $T$, every ring homomorphism $\varphi : B \to T$ and every $h \in T[X]$, the polynomial $h$ is a two-kernel for the curve $W$ mapped along $\varphi$ if and only if there is exactly one ring homomorphism $\psi : C \to T$ with $\psi$ restricting to $\varphi$ on $B$ and with $h_u$ pushed forward along $\psi$ equal to $h$.
--
--   This is the representability, by a module-finite algebra over the base, of the functor of $\Gamma_0(2)$-type level structures on a fixed Weierstrass curve, namely of monic linear divisors of its $2$-division polynomial. It feeds the corresponding statement for tuples of prime-power level structures, [`ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple`](thm.html#ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (h2 : IsUnit ((2 : ℕ) : B)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsTwoKernel hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsTwoKernel h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by sorry
