-- Prove2me | Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit_of_even
-- name    : WeierstrassCurve.separable_prePsi_of_isUnit_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/865c895e-0616-5147-8497-36f30a221544
-- title:
--   Separability of even division polynomials preΨ'ₙ
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with discriminant $W.\Delta$. Let $n$ be a natural number, assumed even, and assume that the element $n \cdot W.\Delta$ of $R$ (the image of $n$ under the canonical map $\mathbb{N} \to R$ times the discriminant) is a unit of $R$. The conclusion is that the univariate polynomial $W.\mathrm{pre}\Psi'\,n \in R[X]$ is separable in Mathlib's sense, that is, that it is coprime to its formal derivative: there exist $a, b \in R[X]$ with $a \cdot (W.\mathrm{pre}\Psi'\,n) + b \cdot (W.\mathrm{pre}\Psi'\,n)' = 1$. Here $\mathrm{pre}\Psi'$ is the univariate factor of the division polynomials: for even $n$ the bivariate $n$-division polynomial of $W$ is $(W.\mathrm{pre}\Psi'\,n)$ times $2Y + a_1X + a_3$, and $W.\mathrm{pre}\Psi'\,n$ has degree $(n^2-4)/2$ with leading coefficient $n/2$ when $n \ge 2$. Note that the hypothesis is invertibility of the single product $n \cdot W.\Delta$, which is equivalent to invertibility of $n$ and of $W.\Delta$ separately; no further assumption on $R$ (such as being reduced or a field) is made.
--
--   This is the standard statement that the $n$-division polynomial of an elliptic curve has simple roots once $n$ and the discriminant are invertible, in the form for even $n$, the abscissae of the $n$-torsion points that are not $2$-torsion being pairwise distinct. It is used in the project wherever roots of division polynomials are counted or lifted, for instance in the analysis of cyclic kernels of isogenies and of $\Gamma_0$-structures; its proof passes from the case of an algebraically closed field, where the $n$-torsion has exactly $n^2$ points and the involution $P \mapsto -P$ has only the $2$-torsion as fixed points, to an arbitrary base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_separable_prePsi_of_isUnit_of_even.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Polynomial

theorem WeierstrassCurve.separable_prePsi_of_isUnit_of_even
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) {n : ℕ} (hn : Even n)
    (hu : IsUnit ((n : R) * W.Δ)) : (W.preΨ' n).Separable := by sorry
