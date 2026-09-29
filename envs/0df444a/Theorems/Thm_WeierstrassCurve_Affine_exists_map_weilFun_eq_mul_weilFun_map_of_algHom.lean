-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom
-- name    : WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/136a6cc4-db3a-54f6-92de-64ee35e58f08
-- title:
--   Base change of the Weil function along an F-embedding
-- statement:
--   Let $F$, $K$, $K'$ be fields with $K$ and $K'$ algebraically closed $F$-algebras, let $W$ be a Weierstrass curve over $F$ which is elliptic, and assume the affine coordinate rings of the base changes $W⁄K$ and $W⁄K'$ are Dedekind domains. Let $n$ be a natural number whose image in $K$ is nonzero, let $f : K \to K'$ be an $F$-algebra homomorphism, and let $\Phi$ be a ring homomorphism from the function field of $W⁄K$ to that of $W⁄K'$ which is compatible with coefficientwise base change along $f$, in the sense that for every bivariate polynomial $p$ over $K$ the image under $\Phi$ of the class of $p$ in the coordinate ring of $W⁄K$ equals the class of $p.map(f)$ in the coordinate ring of $W⁄K'$. Let $T$ be a point of $W⁄K$ with $n \cdot T = 0$. Then there is a unit $c$ of $K'$ with $\Phi(\mathrm{weilFun}\, W\, K\, n\, T) = c \cdot \mathrm{weilFun}\, W\, K'\, n\, (f_* T)$ inside the function field of $W⁄K'$, where $f_* T$ is the image of $T$ under the map of point groups induced by $f$, $c$ is viewed in the function field via the structure map, and $\mathrm{weilFun}\, W\, L\, n\, S$ denotes the quotient of the image of $\mathrm{weilNum}\, W\, L\, n\, S$ by that of $\mathrm{weilNum}\, W\, L\, n\, 0$, each $\mathrm{weilNum}$ being a chosen generator of the corresponding fibre ideal when that ideal is principal and $1$ otherwise.
--
--   This is the transport of Silverman's Weil function $g_T$, with divisor $[n]^*(T)-[n]^*(O)$, under a base change of algebraically closed coefficient fields: $g_T$ goes to a nonzero constant multiple of $g_{f(T)}$. It is used to show that the Weil pairing constructed from these functions is compatible with $F$-embeddings of algebraically closed fields, in [`WeierstrassCurve.Affine.weilPairing0_map_algHom`](thm.html#WeierstrassCurve.Affine.weilPairing0_map_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain WithZero
open WeierstrassCurve
open WeierstrassCurve.Affine
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) :
    ∃ c : K'ˣ, Φ (weilFun W K n T) =
      algebraMap K' (W⁄K').FunctionField (c : K') * weilFun W K' n (WeierstrassCurve.Affine.Point.map f T) := by sorry
