-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
-- name    : WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/2444aae1-be93-5d1a-b696-00e31bad4857
-- title:
--   Translation invariance of the Weil function g_T up to a constant
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed, and let $W$ be a Weierstrass curve over $F$ which is elliptic; assume the coordinate ring of the affine base-changed curve $W\!\!\upharpoonright\! K$ is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, and let $S$ and $T$ be points of the group of $K$-points of the affine curve with $(n : \mathbb{Z}) \cdot S = 0$ and $(n : \mathbb{Z}) \cdot T = 0$. Write $g_T$ for `weilFun W K n T`, the element of the function field obtained as the quotient of the image of `weilNum W K n T` by the image of `weilNum W K n 0`, where `weilNum W K n T` is a chosen generator of the ideal `fibIdeal W K n T` when that ideal is principal and $1$ otherwise; and write $\tau_S^*$ for `transEquiv W K S`, the $K$-algebra automorphism of the function field given by `transPull W K S` with inverse `transPull W K (-S)`. The conclusion asserts the existence of a unit $c \in K^\times$ with $\tau_S^*(g_T) = \iota(c)\, g_T$, where $\iota$ is the structure map $K \to (W\!\!\upharpoonright\! K).\mathrm{FunctionField}$.
--
--   This is the invariance step in the construction of the Weil pairing: the function $g_T$ with divisor $[n]^*(T) - [n]^*(O)$ is, up to a multiplicative constant, unchanged by translation by an $n$-torsion point $S$, and that constant is the pairing value $e_n(S,T)$. It is used by the statements establishing the basic properties of `weilPairing0`, including bilinearity in the first variable and nondegeneracy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) = algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T := by sorry
