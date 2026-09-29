-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom
-- name    : WeierstrassCurve.Affine.map_transEquiv_eq_transEquiv_map_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/2ae5bef6-90ba-5539-8ad5-bfc4f9435a83
-- title:
--   Translation pull-back commutes with base change of scalars
-- statement:
--   Let $F$, $K$, $K'$ be fields with $K$ and $K'$ $F$-algebras, equipped with decidable equality and assumed algebraically closed, let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant), and let $f\colon K\to K'$ be an $F$-algebra homomorphism. Write $(W⁄K)$ for the affine curve obtained from $W$ by base change to $K$, with coordinate ring $(W⁄K).\mathrm{CoordinateRing}$ and function field $(W⁄K).\mathrm{FunctionField}$ its fraction field. Let $\Phi\colon (W⁄K).\mathrm{FunctionField}\to (W⁄K').\mathrm{FunctionField}$ be a ring homomorphism which is coefficientwise base change along $f$ in the following sense: for every bivariate polynomial $p\in K[X][Y]$, $\Phi$ carries the image in the function field of the class `CoordinateRing.mk (W⁄K) p` to the image of the class `CoordinateRing.mk (W⁄K') (p.map (mapRingHom f))` of the polynomial obtained by applying $f$ to all coefficients. Let $S$ be a point of $(W⁄K)$ (affine point or the point at infinity) and $h$ an element of $(W⁄K).\mathrm{FunctionField}$. The conclusion is $\Phi(\mathrm{transEquiv}\,W\,K\,S\,(h)) = \mathrm{transEquiv}\,W\,K'\,(\mathrm{Point.map}\,f\,S)\,(\Phi(h))$, where $\mathrm{transEquiv}\,W\,K\,S$ is the $K$-algebra automorphism of the function field given by pull-back along translation by $S$ (built from the pull-back homomorphism attached to the sum of the generic point and the base change of $S$, with the pull-back attached to $-S$ as inverse), and $\mathrm{Point.map}\,f\,S$ is the point of $(W⁄K')$ obtained by applying $f$ to the coordinates of $S$.
--
--   This is the statement that the translation-pull-back automorphism $\tau_S^{*}$ of the function field of an elliptic curve is defined over the field of definition of $S$, hence commutes with extension of scalars along any $F$-homomorphism of algebraically closed fields. It is used in establishing the compatibility of the Weil pairing construction with such base changes, in [`WeierstrassCurve.Affine.weilPairing0_map_algHom`](thm.html#WeierstrassCurve.Affine.weilPairing0_map_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.map_transEquiv_eq_transEquiv_map_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic] (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    Φ (transEquiv W K S h) = transEquiv W K' (WeierstrassCurve.Affine.Point.map f S) (Φ h) := by sorry
