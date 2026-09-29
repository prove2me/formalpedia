-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_self
-- name    : WeierstrassCurve.Affine.weilPairing0_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/cf6dc533-517b-53f2-9aed-82e87b4f7cc1
-- title:
--   The pairing e₀ is trivial on the diagonal: e₀(T,T)=1
-- statement:
--   Let $F$ be a field, $K$ an algebraically closed field which is an $F$-algebra, and $W$ a Weierstrass curve over $F$ which is elliptic, such that the coordinate ring of the base-changed affine curve $W⁄K$ is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, and let $T$ be a point of $(W⁄K)$ annihilated by $n$, i.e. $(n : \mathbb{Z}) \bullet T = 0$. Then the unit $\mathrm{weilPairing0}\ W\ K\ n\ T\ T$ of $K$ equals $1$. Here $\mathrm{weilFun}\ W\ K\ n\ T$ is the element $g_T$ of the function field of $W⁄K$ obtained as the quotient of the images of `weilNum W K n T` and `weilNum W K n 0` under the map to the function field, $\mathrm{transEquiv}\ W\ K\ S$ is the $K$-algebra automorphism of that function field built from the translation pull-backs along $S$ and $-S$, and $\mathrm{weilPairing0}\ W\ K\ n\ S\ T$ is, by definition, a chosen unit $c \in K^{\times}$ with $\mathrm{transEquiv}\ W\ K\ S\ (g_T) = c \cdot g_T$ if such a unit exists, and $1$ otherwise. Thus the assertion is that for $S = T$ the constant relating $\tau_T^{*} g_T$ to $g_T$ is $1$.
--
--   This is the classical statement that the Weil pairing is alternating on the diagonal, $e_n(T,T) = 1$, here for the function-field-level pairing $e_0$ attached to $n$-torsion points over an algebraically closed field. It is used in the treatment of level structures on modular curves, in particular in identifying the determinant of the action of a matrix on the kernel of a classifying map and in the recognition of elements of $\Gamma$ by their effect on the pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_weilPairing0_self.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.weilPairing0_self {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0) : weilPairing0 W K n T T = 1 := by sorry
