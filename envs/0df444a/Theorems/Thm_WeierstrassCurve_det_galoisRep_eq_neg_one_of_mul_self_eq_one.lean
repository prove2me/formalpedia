-- Prove2me | Theorems.Thm_WeierstrassCurve_det_galoisRep_eq_neg_one_of_mul_self_eq_one
-- name    : WeierstrassCurve.det_galoisRep_eq_neg_one_of_mul_self_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/690dabe6-1ba9-5d4e-9784-989cf25923b1
-- title:
--   Involutions act on p-torsion with determinant -1
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, and assume $K$ is algebraically closed of characteristic zero. Let $W$ be a Weierstrass curve over $F$ that is elliptic, and let $p$ be a prime. Let $c$ be an $F$-algebra automorphism of $K$ with $c\cdot c = 1$ and $c \neq 1$, that is, an involution of $K$ over $F$ other than the identity. Consider the $p$-torsion submodule $\mathrm{Submodule.torsionBy}\ \mathbb{Z}\ (W\!\!\;⁄K).\mathrm{Point}\ p$ of the group of points of the affine model of $W$ base changed to $K$, regarded as a module over $\mathbb{Z}/p$, and let `galoisRepModuleEnd F W p` be the monoid homomorphism sending an automorphism of $K$ over $F$ to the $\mathbb{Z}/p$-linear endomorphism of this $p$-torsion module given by its natural action on points. The assertion is that the determinant of `galoisRepModuleEnd F W p c` equals $-1$ in $\mathbb{Z}/p$.
--
--   This is the oddness of the mod $p$ representation attached to an elliptic curve: a complex conjugation acts on the $p$-torsion with determinant $-1$, since the determinant of the representation is the mod $p$ cyclotomic character. It is used in the statement that the trace of a complex conjugation vanishes and its determinant is $-1$, and in the verification that the residual representation attached to an elliptic curve is odd.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_det_galoisRep_eq_neg_one_of_mul_self_eq_one.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.det_galoisRep_eq_neg_one_of_mul_self_eq_one {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [CharZero K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} (hp : p.Prime) (c : K ≃ₐ[F] K) (hc : c * c = 1) (hc1 : c ≠ 1) : LinearMap.det (galoisRepModuleEnd F W p c) = -1 := by sorry
