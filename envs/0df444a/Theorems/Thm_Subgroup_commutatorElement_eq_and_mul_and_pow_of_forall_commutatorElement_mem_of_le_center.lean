-- Prove2me | Theorems.Thm_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
-- name    : Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/e82b368e-8aae-5833-89b6-ac8307953dbe
-- title:
--   Central commutators give a bimultiplicative alternating pairing
-- statement:
--   Let $G$ be a group and let $Z$ be a subgroup of $G$ with $Z \le Z(G)$, and suppose every commutator $⁅g,h⁆ = ghg^{-1}h^{-1}$ of elements of $G$ lies in $Z$. Then the following six assertions hold simultaneously: (i) the commutator depends only on the cosets of its arguments, i.e. for all $g,g',h,h' \in G$ with $g^{-1}g' \in Z$ and $h^{-1}h' \in Z$ one has $⁅g,h⁆ = ⁅g',h'⁆$; (ii) $⁅gg',h⁆ = ⁅g,h⁆\,⁅g',h⁆$ for all $g,g',h$; (iii) $⁅g,hh'⁆ = ⁅g,h⁆\,⁅g,h'⁆$ for all $g,h,h'$; (iv) $⁅g,h⁆\,⁅h,g⁆ = 1$ for all $g,h$; (v) $⁅g,g⁆ = 1$ for all $g$; and (vi) for all $g,h \in G$ and all $n \in \mathbb{N}$, both $⁅g^n,h⁆ = ⁅g,h⁆^n$ and $⁅g,h^n⁆ = ⁅g,h⁆^n$. The conclusion is stated as a single conjunction of these six universally quantified identities in $G$, rather than as a homomorphism or pairing on $G/Z$.
--
--   This is the standard commutator calculus in a group of nilpotency class at most two: when all commutators are central, the commutator map is bimultiplicative, skew-symmetric and alternating, and factors through $G/Z$. It is used in the construction of the commutator pairing attached to a theta group, supplying the additivity, skew-symmetry and level properties of the Riemann pairing on an abelian variety.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped commutatorElement

theorem Subgroup.commutatorElement_eq_and_mul_and_pow_of_forall_commutatorElement_mem_of_le_center
    {G : Type*} [Group G] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z) :
    (∀ g g' h h' : G, g⁻¹ * g' ∈ Z → h⁻¹ * h' ∈ Z → ⁅g, h⁆ = ⁅g', h'⁆) ∧
    (∀ g g' h : G, ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆) ∧
    (∀ g h h' : G, ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆) ∧
    (∀ g h : G, ⁅g, h⁆ * ⁅h, g⁆ = 1) ∧
    (∀ g : G, ⁅g, g⁆ = 1) ∧
    (∀ (g h : G) (n : ℕ), ⁅g ^ n, h⁆ = ⁅g, h⁆ ^ n ∧ ⁅g, h ^ n⁆ = ⁅g, h⁆ ^ n) := by sorry
