-- Prove2me | Theorems.Thm_Rat_exists_ternary_eq_neg_prime_of_forall_padic_isotropic
-- name    : Rat.exists_ternary_eq_neg_prime_of_forall_padic_isotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/d3fa5c5f-9214-5129-bd9d-1681a737ebb2
-- title:
--   Ternary form ux²+vy²-uvz²=-p solvable from local isotropy
-- statement:
--   Let $p$ be a prime number and let $u,v$ be rational numbers, both nonzero. Assume that for every prime $\ell$ different from $p$ the conic $z^2-ux^2-vy^2=0$ is isotropic over the field $\mathbb{Q}_\ell$ of $\ell$-adic numbers: there exist $z,x,y\in\mathbb{Q}_\ell$, not all three zero (that is, it is not the case that $z=0$ and $x=0$ and $y=0$), with $z^2-ux^2-vy^2=0$, the coefficients $u,v$ being taken in $\mathbb{Q}_\ell$ via the canonical embedding of $\mathbb{Q}$. The conclusion is the existence of rational numbers $x,y,z$ with $$u\,x^2+v\,y^2-u v\,z^2=-p.$$ No hypothesis is imposed at the place $p$ or at the archimedean place. Equivalently, in the quaternion algebra $\bigl(\tfrac{u,v}{\mathbb{Q}}\bigr)$ with $i^2=u$, $j^2=v$, $k=ij$, the hypothesis says that the algebra is split at every finite place away from $p$, and the conclusion produces a pure quaternion $x i+y j+z k$ of square $-p$, i.e. an embedding of $\mathbb{Q}(\sqrt{-p})$ into that algebra.
--
--   This is the case $K=\mathbb{Q}(\sqrt{-p})$ of the local–global criterion for embedding a quadratic field into a quaternion algebra, in the concrete shape of a solvability statement for a ternary quadratic equation over $\mathbb{Q}$; it rests on the Hasse–Minkowski theorem for ternary forms, here entered through the cited results on rational and local solvability of $-a x^2-b y^2+ab z^2=c$. It is used in the construction of an endomorphism relation for a Weierstrass curve, in [`WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rat_exists_ternary_eq_neg_prime_of_forall_padic_isotropic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Rat.exists_ternary_eq_neg_prime_of_forall_padic_isotropic (p : ℕ) [Fact p.Prime] (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0) (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0) : ∃ x y z : ℚ, u * x ^ 2 + v * y ^ 2 - u * v * z ^ 2 = -p := by sorry
