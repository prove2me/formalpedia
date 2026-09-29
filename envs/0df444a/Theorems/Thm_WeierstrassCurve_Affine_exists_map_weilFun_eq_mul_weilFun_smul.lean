-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_smul
-- name    : WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4cabc47d-2752-5485-b03e-065ffa2feb5d
-- title:
--   Galois conjugation of the Weil function up to a constant
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed, and let $W$ be a Weierstrass curve over $F$ that is elliptic, such that the coordinate ring of the base change $W\!\restriction_K$ (written `W⁄K`) is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, let $\sigma$ be an $F$-algebra automorphism of $K$, and let $\Phi$ be a ring endomorphism of the function field of `W⁄K` which, on classes of bivariate polynomials, is coefficientwise conjugation by $\sigma$: for every $p \in K[X][Y]$, $\Phi$ sends the image in the function field of the coordinate-ring class of $p$ to the image of the class of the polynomial obtained by applying $\sigma$ to all coefficients of $p$. Finally let $T$ be a point of `W⁄K` with $n \cdot T = 0$. The assertion is that there exists a unit $c$ of $K$ with $\Phi(\mathtt{weilFun}\,W\,K\,n\,T) = c \cdot \mathtt{weilFun}\,W\,K\,n\,(\sigma \bullet T)$, where $\mathtt{weilFun}\,W\,K\,m\,S$ denotes the quotient, inside the function field, of the images of the chosen generators of the ideals `fibIdeal W K m S` and `fibIdeal W K m 0` (the generator being taken when the ideal is principal, and $1$ otherwise), and $\sigma \bullet T$ is the action of $\sigma$ on points.
--
--   This is the statement that the function $g_T$ underlying the construction of the Weil pairing on $n$-torsion is Galois-equivariant up to a multiplicative constant: conjugating $g_T$ by $\sigma$ yields a constant multiple of $g_{\sigma T}$. It is used in the proof of the Galois equivariance of the Weil pairing, [`WeierstrassCurve.Affine.weilPairing0_galois`](thm.html#WeierstrassCurve.Affine.weilPairing0_galois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_smul.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_smul {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (σ : K ≃ₐ[F] K) (Φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField) (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) = algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K))))) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) : ∃ c : Kˣ, Φ (weilFun W K n T) = algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n (σ • T) := by sorry
