-- Prove2me | Theorems.Thm_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
-- name    : Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/b5a471b6-7e05-5b2b-9c8e-8a8b6952ddd3
-- title:
--   Quotient by an involution under quadratic trace relations mod M
-- statement:
--   Let $M$ be a natural number with $3 \le M$, let $H$ be a finite commutative group, let $c \in H$ satisfy $c \cdot c = 1$, and let $\chi : H \to (\mathbb{Z}/M)^{\times}$ be an injective group homomorphism whose value at $c$ has image $-1$ in $\mathbb{Z}/M$. Assume further a trace condition: for every $h \in H$ there is an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that, writing $\lambda$ for the image of $\chi(h)$ in $\mathbb{Z}/M$, one has $\lambda^2 - t\lambda + 1 = 0$ in $\mathbb{Z}/M$, and moreover $t = 2$ forces $h = 1$ while $t = -2$ forces $h = c$. The conclusion is a conjunction of four assertions about the quotient group $H / \langle c \rangle$, where $\langle c \rangle$ is the subgroup of integer powers of $c$: its cardinality is at most $3$; it is cyclic; if $2$ divides its cardinality then there exists $\lambda \in \mathbb{Z}/M$ with $\lambda^2 + 1 = 0$; and if $3$ divides its cardinality then there exists $\lambda \in \mathbb{Z}/M$ with $\lambda^2 + \lambda + 1 = 0$.
--
--   This is the purely group-theoretic step behind the control of automorphism groups at supersingular points: $H$ plays the role of a group of automorphisms acting faithfully on a level-$M$ structure, $c$ the automorphism $[-1]$, and $t$ the trace of an automorphism, whose characteristic relation $\lambda^2 - t\lambda + 1 = 0$ with $|t| \le 2$ is what the moduli dictionary supplies. It is used in the two results on the cyclicity of inertia, and on the non-divisibility of its order, at supersingular points of the two-chart integral model of $X_1(\cdot)/\Gamma_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
    (M : ℕ) (hM : 3 ≤ M) (H : Type*) [CommGroup H] [Finite H]
    (c : H) (hc2 : c * c = 1)
    (χ : H →* (ZMod M)ˣ) (hχ : Function.Injective χ) (hc : ((χ c : (ZMod M)ˣ) : ZMod M) = -1)
    (htr : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      ((χ h : (ZMod M)ˣ) : ZMod M) ^ 2 - (t : ZMod M) * ((χ h : (ZMod M)ˣ) : ZMod M) + 1 = 0 ∧
      (t = 2 → h = 1) ∧ (t = -2 → h = c)) :
    Nat.card (H ⧸ Subgroup.zpowers c) ≤ 3 ∧ IsCyclic (H ⧸ Subgroup.zpowers c) ∧
      (2 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + 1 = 0) ∧
      (3 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + lam + 1 = 0) := by sorry
