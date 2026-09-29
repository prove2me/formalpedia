-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
-- name    : WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/67d88703-e2db-5079-b114-3d22f5c5ad77
-- title:
--   Integral Weil numerator along a valuation subring
-- statement:
--   Let $K$ be an algebraically closed field, $\mathcal O \subseteq K$ a valuation subring, $\Omega$ an algebraically closed field and $\psi : \mathcal O \to \Omega$ a ring homomorphism. Let $W$ be a Weierstrass curve over $\mathcal O$ satisfying `IsElliptic`, let $n$ be a natural number whose image in $\mathcal O$ is a unit, and let $T_K$, $T_\Omega$ be points of the affine curves obtained from $W$ by base change along $\mathcal O \hookrightarrow K$ and along $\psi$. Assume that either both $T_K$ and $T_\Omega$ are the point at infinity, or there are $x_T, y_T \in \mathcal O$ whose images are nonsingular points of both base changes and $T_K$, $T_\Omega$ are the corresponding affine points; assume also $n \cdot T_K = 0$ and $n \cdot T_\Omega = 0$. Then there are polynomials $p, q \in \mathcal O[X]$ and nonzero scalars $c \in K$, $c' \in \Omega$ such that, in the coordinate ring of the base change of $W$ to $K$, the element $p \cdot 1 + q \cdot \bar Y$ (coefficients mapped into $K$, acting through the polynomial-module structure) equals $c$ times `weilNum` of $n$ and $T_K$, and likewise the images of $p, q$ under $\psi$ give $c'$ times `weilNum` of $n$ and $T_\Omega$ in the coordinate ring of the base change along $\psi$. Here `weilNum` of $n$ and $T$ is a chosen generator of the ideal `fibIdeal`, the product of the ideals `placeIdeal W K P` over the points $P$ of the finite set `fibSet W K n T` (the unit ideal if that set is infinite), and is $1$ if that ideal is not principal.
--
--   This is the divisor-level form of the compatibility of the Weil pairing with reduction: a function cutting out the fibre of multiplication by $n$ over an integral torsion point can be normalised to have coefficients in the valuation subring, and its reduction along $\psi$ again cuts out the corresponding fibre. It feeds the statement that the Weil pairing of integral torsion points lies in $\mathcal O$ and specialises correctly, [`WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring`](thm.html#WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (TK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Point) (TΩ : ((W.map ψ).baseChange Ω).toAffine.Point)
    (hT : (TK = 0 ∧ TΩ = 0) ∨ ∃ (xT yT : 𝒪)
      (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
      (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT)),
      TK = WeierstrassCurve.Affine.Point.some _ _ hTK ∧ TΩ = WeierstrassCurve.Affine.Point.some _ _ hTΩ)
    (hTKn : (n : ℤ) • TK = 0) (hTΩn : (n : ℤ) • TΩ = 0) :
    ∃ (p q : Polynomial 𝒪) (c : K) (c' : Ω), c ≠ 0 ∧ c' ≠ 0 ∧
      Polynomial.map (algebraMap 𝒪 K) p • (1 : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.CoordinateRing) +
          Polynomial.map (algebraMap 𝒪 K) q •
            WeierstrassCurve.Affine.CoordinateRing.mk ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine Y =
        algebraMap K _ c * weilNum (W.map (algebraMap 𝒪 K)) K n TK ∧
      Polynomial.map ψ p • (1 : ((W.map ψ).baseChange Ω).toAffine.CoordinateRing) +
          Polynomial.map ψ q • WeierstrassCurve.Affine.CoordinateRing.mk ((W.map ψ).baseChange Ω).toAffine Y =
        algebraMap Ω _ c' * weilNum (W.map ψ) Ω n TΩ := by sorry
