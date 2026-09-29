-- Prove2me | Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
-- name    : WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/a6ae4475-f68f-5bc7-a365-f1642a586e13
-- title:
--   E[n](K)≅(ℤ/n)² over an algebraically closed field
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed, and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $n$ be a natural number whose image in $K$ is nonzero, i.e. the characteristic of $K$ does not divide $n$ (this also forces $n \neq 0$). The assertion is that the type of additive group isomorphisms $\mathbb Z/n \times \mathbb Z/n \simeq \mathbb{Z}/n$-free of rank two is nonempty: concretely, `Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W⁄K).Point n)`, where $(W⁄K)$ denotes the base change of $W$ to $K$, $(W⁄K).\mathrm{Point}$ its group of points, and `Submodule.torsionBy ℤ _ n` the subgroup of elements killed by $n$. Thus $W(K)[n] \cong \mathbb Z/n \times \mathbb Z/n$ as abelian groups. The statement is an existence assertion (a `Nonempty` of the type of isomorphisms), not a specified isomorphism, so it provides no canonical choice of basis of the $n$-torsion.
--
--   This is the classical structure theorem for the $n$-torsion of an elliptic curve over an algebraically closed field of characteristic not dividing $n$ (Silverman, Corollary III.6.4(b)), i.e. the geometric existence of a full level-$n$ structure. It underlies the construction of mod-$n$ Galois representations attached to elliptic curves and the counting of cyclic $n$-subgroups, and is cited widely in the modular-curve and Galois-representation parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W⁄K).Point n) := by sorry
