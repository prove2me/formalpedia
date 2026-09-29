-- Prove2me | Theorems.Thm_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- name    : WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/eaf00541-7ecb-5177-9748-b9599be80fbb
-- title:
--   Trivial n-torsion on a cuspidal Weierstrass curve in characteristic zero
-- statement:
--   Let $K$ be a field of characteristic zero and let $W$ be a Weierstrass curve over $K$, given by coefficients $a_1,a_2,a_3,a_4,a_6$. Assume that $W$ is not elliptic in Mathlib's sense, i.e. its discriminant $\Delta$ is not a unit of $K$, and that the invariant $c_4$ of $W$ vanishes; let $n$ be a nonzero natural number. The assertion is that the $n$-torsion submodule $\{P : (n : \mathbb{Z}) \cdot P = 0\}$ of the group $(W \mathbin{/} \overline{K}).\mathrm{Point}$ — the group of points of the affine Weierstrass curve obtained by base change of $W$ to an algebraic closure $\overline{K}$ of $K$, that is, the nonsingular affine points of the cubic together with the point at infinity, under the usual chord-and-tangent addition — regarded as a $\mathbb{Z}$-submodule, is a subsingleton: it has at most one element, and hence consists of the zero point alone. (Equality of $\Delta$ with $0$ is recovered from the failure of invertibility, since $K$ is a field.)
--
--   This is the cuspidal case of the classification of the smooth locus of a singular Weierstrass curve: when $\Delta = c_4 = 0$ the curve has a cusp and its group of nonsingular points over an algebraically closed field of characteristic zero is the additive group, hence torsion-free (Silverman, Prop. III.2.5(a)). It feeds the packaging of torsion on singular Weierstrass curves as a Hopf algebra over a field, via [`WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero`](thm.html#WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ = 0) (n : ℕ) (hn : n ≠ 0) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    Subsingleton (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point (n:ℤ)) := by sorry
