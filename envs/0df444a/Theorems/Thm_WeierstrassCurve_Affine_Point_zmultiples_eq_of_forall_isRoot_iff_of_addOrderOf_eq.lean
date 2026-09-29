-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
-- name    : WeierstrassCurve.Affine.Point.zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/652e3dcf-4c91-53a7-9d7b-1eb6bbf163c2
-- title:
--   Cut-out point generates a cyclic subgroup of order M'
-- statement:
--   Let $\Omega$ be a field with decidable equality, $W$ a Weierstrass curve over $\Omega$, and $M'$ a nonzero natural number. Let $H$ be an additive subgroup of the group of affine points $W(\Omega)$ which is additively cyclic and satisfies $\#H = M'$. Let $h$ assign to each prime $p$ in the prime factors of $M'$ a polynomial $h_p \in \Omega[X]$, assumed nonzero, and suppose that for each such $p$ and each $x_1 \in \Omega$ the element $x_1$ is a root of $h_p$ if and only if there are a point $P \in H$ and a $y_1 \in \Omega$ with $(x_1,y_1)$ nonsingular on $W$ such that $P$ has exact additive order $p^{v_p(M')}$ and $P$ is the affine point with coordinates $(x_1,y_1)$. Let $g \in W(\Omega)$ have exact additive order $M'$ and satisfy the cut-out condition: for every prime $p \mid M'$, every $n \in \mathbb{N}$ and every nonsingular pair $(x_1,y_1)$, if $n \cdot g$ is the affine point $(x_1,y_1)$ and $n \cdot g$ has exact order $p^{v_p(M')}$, then $x_1$ is a root of $h_p$. The conclusion is that the subgroup $\mathbb{Z}\cdot g$ of integer multiples of $g$ equals $H$.
--
--   This is the elementary recognition statement behind the polynomial encoding of a cyclic subgroup of a Weierstrass curve by the $x$-coordinates of the generators of its $p$-primary parts: a point of order $M'$ whose relevant multiples are cut out by the given polynomials generates exactly the encoded subgroup. It is used in the identification of $j$-invariants attached to full level structures at the Tate point, where the point cut out by a base-changed datum must be shown to generate the transported subgroup of order $M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
    (Ω : Type) [Field Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) (M' : ℕ) [NeZero M']
    (H : AddSubgroup W.toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = M')
    (h : ↥M'.primeFactors → Polynomial Ω) (h0 : ∀ p, h p ≠ 0)
    (hroots : ∀ (p : ↥M'.primeFactors) (x₁ : Ω),
      (h p).IsRoot x₁ ↔ ∃ (P : W.toAffine.Point) (y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        P ∈ H ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧ P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (g : W.toAffine.Point)
    (hg : addOrderOf g = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (h p).IsRoot x₁) :
    AddSubgroup.zmultiples g = H := by sorry
