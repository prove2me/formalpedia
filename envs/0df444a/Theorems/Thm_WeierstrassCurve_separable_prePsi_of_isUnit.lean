-- Prove2me | Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
-- name    : WeierstrassCurve.separable_prePsi_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ffb46c86-3728-5010-8024-9a3adf639065
-- title:
--   Separability of the odd division polynomial ψₙ
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with discriminant $W.\Delta$. Let $n$ be a natural number which is odd, and assume that the product $(n : R) \cdot W.\Delta$ of the image of $n$ in $R$ with the discriminant is a unit of $R$ (equivalently, both $n$ and $W.\Delta$ are invertible in $R$). Then the univariate polynomial $W.\mathrm{pre}\Psi' \, n \in R[X]$ — Mathlib's normalised division polynomial, which for odd $n$ is the $n$-division polynomial $\psi_n$ in the abscissa, of degree $(n^2-1)/2$ and leading coefficient $n$ — is separable, i.e. it is coprime to its formal derivative: there exist $a, b \in R[X]$ with $a \cdot (W.\mathrm{pre}\Psi' \, n) + b \cdot (W.\mathrm{pre}\Psi' \, n)' = 1$. No hypothesis of invertibility of $2$, nor any regularity assumption on $R$ beyond commutativity, is imposed; the invertibility of $n \cdot \Delta$ carries the whole statement.
--
--   This is the division-polynomial form of the assertion that, over a base on which $n$ and the discriminant are invertible, the $n$-torsion of a Weierstrass curve is unramified over the base away from the zero section: $R[X]/(\psi_n)$ is then a finite étale $R$-algebra, since $\psi_n$ has unit leading coefficient $n$. It is used in the analysis of $\Gamma_0$-type level structures, where factorisations of $\psi_n$ over suitable base changes produce cyclic subgroup schemes of prescribed order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_separable_prePsi_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.separable_prePsi_of_isUnit {R : Type*} [CommRing R] (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (hu : IsUnit ((n : R) * W.Δ)) : (W.preΨ' n).Separable := by sorry
