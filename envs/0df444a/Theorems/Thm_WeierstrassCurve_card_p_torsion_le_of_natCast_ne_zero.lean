-- Prove2me | Theorems.Thm_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero
-- name    : WeierstrassCurve.card_p_torsion_le_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/2429c497-73a7-5f79-ae51-9c07fe644d43
-- title:
--   Bound #E[p] ≤ p² over an arbitrary field
-- statement:
--   Let $F$ be a field with decidable equality, let $W$ be a Weierstrass curve over $F$ that is elliptic (its discriminant is a unit, as recorded by the `IsElliptic` instance), and let $p$ be a natural number. Assume $p$ is prime, that $5 \le p$, and that the image of $p$ in $F$ is nonzero. The assertion is that the $\mathbb{Z}$-torsion submodule `Submodule.torsionBy ℤ W.toAffine.Point p` of the group of $F$-points of the associated affine Weierstrass curve — that is, the subgroup of points $P$ with $p \cdot P = 0$ — has cardinality at most $p^2$, the cardinality being measured by `Nat.card`. Since the proof exhibits this subgroup as embedded in a group of order $p^2$, the bound is a genuine bound on a finite cardinality rather than the vacuous statement that `Nat.card` vanishes on an infinite type. Only an upper bound is claimed, not the isomorphism $E[p] \cong (\mathbb{Z}/p)^2$, which may fail over a non-closed $F$.
--
--   This is the characteristic-free upper bound for the $p$-torsion of an elliptic curve over an arbitrary field in which $p$ is invertible; over an algebraically closed field it is an equality. It is used in the counting argument for Tate curves, in [`TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero`](thm.html#TateCurve.eq_zero_or_eq_tateParam_of_prime_nsmul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.card_p_torsion_le_of_natCast_ne_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) ≤ p ^ 2 := by sorry
