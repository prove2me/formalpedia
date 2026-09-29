-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv
-- name    : WeierstrassCurve.Affine.valuation_placeOf_smul_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/960a1d3b-121f-50c9-9eb3-f6901fc02dd5
-- title:
--   Galois equivariance of the valuations v_P on K(E)
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, let $W$ be a Weierstrass curve over $F$, and write $W\!\!⁄K$ for its base change to $K$, with coordinate ring $(W⁄K).\mathrm{CoordinateRing}$ and function field $(W⁄K).\mathrm{FunctionField}$. Let $\sigma$ be an $F$-algebra automorphism of $K$ and let $\Phi$ be a ring endomorphism of $(W⁄K).\mathrm{FunctionField}$ which is assumed to act on the image of the coordinate ring by applying $\sigma$ to coefficients: for every bivariate polynomial $p \in K[X][Y]$, $\Phi$ sends the image of the class $\mathrm{CoordinateRing.mk}\,(W⁄K)\,p$ in the function field to the image of the class of the polynomial obtained from $p$ by mapping all coefficients through $\sigma$. Assume the coordinate ring of $W⁄K$ is a Dedekind domain. Let $P$ be a point of $W⁄K$ with $P \neq 0$ and with $\sigma \bullet P \neq 0$, and let $f$ be any element of the function field. Here, for a nonzero point $Q$, $\mathrm{placeOf}\,W\,K\,Q$ denotes the height-one prime of the coordinate ring given by the ideal $\mathrm{XYIdeal}\,(W⁄K)\,x_Q\,(C\,y_Q)$, that is $(X - x_Q,\ Y - y_Q)$, which is maximal and nonzero. The conclusion is that the valuation of the function field attached to the place of $\sigma \bullet P$, evaluated at $\Phi f$, equals the valuation attached to the place of $P$, evaluated at $f$.
--
--   This is the Galois equivariance of the orders of vanishing on an affine Weierstrass curve, $\operatorname{ord}_{\sigma P}(f^{\sigma}) = \operatorname{ord}_{P}(f)$, i.e. the statement that a semilinear substitution of coefficients permutes the places $\mathfrak m_P = (X - x_P, Y - y_P)$ compatibly with the action on points. It is used in [`WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul`](thm.html#WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul), where it shows that the conjugate of a function with prescribed divisor and the corresponding function attached to the translated point have the same divisor, as in the proof of Galois invariance of the Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.lean

import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.valuation_placeOf_smul_of_algEquiv {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K) (Φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField) (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) = algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K))))) [IsDedekindDomain (W⁄K).CoordinateRing] {P : (W⁄K).Point} (hP : P ≠ 0) (hσP : σ • P ≠ 0) (f : (W⁄K).FunctionField) : (placeOf W K (σ • P) hσP).valuation (W⁄K).FunctionField (Φ f) = (placeOf W K P hP).valuation (W⁄K).FunctionField f := by sorry
