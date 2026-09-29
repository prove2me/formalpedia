-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one
-- name    : WeierstrassCurve.Affine.eq_zero_of_forall_weilPairing0_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/3353d922-0b40-5590-b83b-3dad9a4c56f9
-- title:
--   Non-degeneracy of the Weil pairing: trivial pairing forces T = O
-- statement:
--   Let $F$ and $K$ be fields with $K$ an algebra over $F$ and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ which is elliptic, and assume the coordinate ring of the affine base change $W⁄K$ is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, and let $T$ be a $K$-point of $W⁄K$ with $(n : \mathbb{Z}) \cdot T = 0$. Suppose that for every point $S$ of $W⁄K$ with $(n : \mathbb{Z}) \cdot S = 0$ one has `weilPairing0 W K n S T = 1`, that is: the unit of $K$ attached to the pair $(S,T)$ — chosen, when it exists, so that the translation automorphism `transEquiv W K S` of the function field of $W⁄K$ (the $K$-algebra automorphism given by pullback along translation by $S$, with inverse the pullback along translation by $-S$) sends the Weil function $g_T =$ `weilFun W K n T`, the ratio of the images in the function field of `weilNum W K n T` and `weilNum W K n 0`, to the scalar multiple of $g_T$ by that unit, and taken to be $1$ when no such unit exists — is trivial. Then $T = 0$.
--
--   This is the non-degeneracy half of the Weil pairing on $n$-torsion: a point of $E[n]$ pairing trivially with all of $E[n]$ is the origin. Together with the bilinearity, alternation and Galois-equivariance of `weilPairing0` it makes the pairing perfect, and it is used in the study of level structures on modular curves, for instance in identifying determinants of elements acting trivially on the relevant torsion data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve IsDedekindDomain WithZero
open WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.eq_zero_of_forall_weilPairing0_eq_one {F K : Type*} [Field F] [Field K] [Algebra F K]
    [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0)
    (h : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → weilPairing0 W K n S T = 1) : T = 0 := by sorry
