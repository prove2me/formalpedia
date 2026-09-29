-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom
-- name    : WeierstrassCurve.Affine.valuation_placeOf_map_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/aeb1909c-a670-5354-825f-ad259c8aebb3
-- title:
--   Base change of a function: valuations at old and new points
-- statement:
--   Let $F$, $K$, $K'$ be fields with $K$ and $K'$ algebras over $F$, with $K$ algebraically closed, and let $W$ be an elliptic Weierstrass curve over $F$ whose coordinate rings $(W⁄K)$ and $(W⁄K')$ after base change are Dedekind domains. Let $f \colon K \to K'$ be an $F$-algebra homomorphism, and let $\Phi$ be a ring homomorphism from the function field of $W⁄K$ to that of $W⁄K'$ which is compatible with coefficientwise base change along $f$: for every bivariate polynomial $p \in K[X][Y]$, $\Phi$ sends the image in the function field of the class of $p$ in the coordinate ring of $W⁄K$ to the image of the class of $p.map(f)$ in the coordinate ring of $W⁄K'$. Let $h$ be an element of the function field of $W⁄K$. Here, for a nonzero affine point $P$, `placeOf` denotes the height-one prime of the relevant coordinate ring cut out by the ideal $(X - x_P,\, Y - y_P)$, which is maximal, hence prime, and nonzero. The conclusion is twofold. First, for every nonzero point $P$ of $W⁄K$ whose image under $f$ is again nonzero, the valuation of $\Phi h$ at the place of the image point equals the valuation of $h$ at the place of $P$. Second, if $h \neq 0$, then for every nonzero point $P'$ of $W⁄K'$ that is not the image under $f$ of any point of $W⁄K$, the valuation of $\Phi h$ at the place of $P'$ equals $1$, i.e. $\Phi h$ has neither a zero nor a pole there.
--
--   This is the statement that the divisor of a base-changed rational function is the base change of its divisor: when $K$ is algebraically closed, no new zeros or poles appear over $K'$ and the orders at $K$-rational points are preserved. It is the homomorphism version of the corresponding statement for automorphisms of $K$, and it is used in [`WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom`](thm.html#WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom) in the transport of the Weil pairing along field homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.valuation_placeOf_map_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (h : (W⁄K).FunctionField) :
    (∀ (P : (W⁄K).Point) (hP : P ≠ 0) (hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0),
        (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).valuation (W⁄K').FunctionField (Φ h) =
          (placeOf W K P hP).valuation (W⁄K).FunctionField h) ∧
    (h ≠ 0 → ∀ (P' : (W⁄K').Point) (hP' : P' ≠ 0),
        (∀ P : (W⁄K).Point, WeierstrassCurve.Affine.Point.map f P ≠ P') →
        (placeOf W K' P' hP').valuation (W⁄K').FunctionField (Φ h) = 1) := by sorry
