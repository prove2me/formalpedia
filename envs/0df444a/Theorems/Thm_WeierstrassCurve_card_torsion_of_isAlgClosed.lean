-- Prove2me | Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
-- name    : WeierstrassCurve.card_torsion_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/11439a28-4f47-513e-b777-e6e7e1abad80
-- title:
--   The n-torsion of an elliptic curve has n² points
-- statement:
--   Let $F$ be a field, let $K$ be an algebraically closed field equipped with an $F$-algebra structure, and let $W$ be a Weierstrass curve over $F$ which is elliptic (its discriminant is a unit). Let $n$ be a natural number whose image in $K$ is nonzero, i.e. the characteristic of $K$ does not divide $n$; in particular $n \neq 0$. Write $W⁄K$ for the base change of $W$ along $F \to K$ and $(W⁄K)$`.Point` for the group of $K$-points of the associated affine Weierstrass curve, consisting of the point at infinity together with the nonsingular affine solutions, with its usual chord-and-tangent group law, viewed as a $\mathbb{Z}$-module. The assertion is that the $n$-torsion submodule $\{P : n \cdot P = 0\}$ of this group has exactly $n^2$ elements, in the sense that its `Nat.card` equals $n^2$; since $n^2 \neq 0$, this includes the assertion that the $n$-torsion is finite. This is the counting form of the statement $E[n] \cong (\mathbb{Z}/n\mathbb{Z})^2$: the group structure of the $n$-torsion is not asserted here, only its cardinality.
--
--   This is the standard computation of the order of the $n$-torsion of an elliptic curve over an algebraically closed field of characteristic not dividing $n$, classically obtained from the division polynomials or from the degree of the multiplication-by-$n$ isogeny. It underlies the construction of the mod-$p$ and $p$-adic Galois representations attached to an elliptic curve, supplying the two-dimensionality of $E[p]$ over $\mathbb{F}_p$, and is used throughout the development downstream of the Galois-representation definitions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.card_torsion_of_isAlgClosed {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 := by sorry
