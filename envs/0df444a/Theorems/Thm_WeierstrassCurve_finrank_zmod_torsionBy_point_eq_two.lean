-- Prove2me | Theorems.Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
-- name    : WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/8e531ec5-7b4c-55ef-948b-6db6af45419c
-- title:
--   E(K)[p] has dimension two over mathbf Fₚ
-- statement:
--   Let $F$ and $K$ be fields with $K$ an algebra over $F$ and $K$ algebraically closed, let $E$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant, in the sense of the Mathlib class `IsElliptic`), and let $p$ be a prime number whose image in $F$ is nonzero. Consider the group of points of the affine Weierstrass curve obtained from $E$ by base change to $K$, i.e. $E(K)$ with its Mathlib group structure, regarded as a $\mathbb Z$-module, and inside it the submodule $\mathrm{torsionBy}\,\mathbb Z\,E(K)\,p$ of elements killed by $p$. This $p$-torsion carries a $\mathbb Z/p\mathbb Z$-module structure, and the assertion is that its rank over $\mathbb Z/p\mathbb Z$, in the sense of `Module.finrank`, equals $2$. Since `Module.finrank` vanishes on modules that are not of finite rank, the statement implicitly contains the finiteness of $E(K)[p]$; equivalently, $E(K)[p] \cong (\mathbb Z/p\mathbb Z)^2$. The hypothesis $(p : F) \neq 0$ covers both characteristic $0$ and characteristic $\ell \neq p$.
--
--   This is the classical statement that the $p$-torsion of an elliptic curve over an algebraically closed field of characteristic prime to $p$ is a two-dimensional $\mathbf F_p$-vector space (Silverman, AEC III.6.4(b)). It is the dimension count that makes the mod $p$ Galois representation attached to an elliptic curve a representation on a plane, and it is used in the determinant computation for Frobenius, in the construction of auxiliary good primes at which the trace condition fails, and in a flatness statement for the multiplication-by-$n$ endomorphism of a Weierstrass model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve F) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) :
    Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = 2 := by sorry
