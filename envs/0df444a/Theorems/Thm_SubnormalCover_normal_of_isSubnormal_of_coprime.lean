-- Prove2me | Theorems.Thm_SubnormalCover_normal_of_isSubnormal_of_coprime
-- name    : SubnormalCover.normal_of_isSubnormal_of_coprime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:43:54.72806+00:00
-- url     : https://prove2.me/theorems/515aec3f-7cde-4448-9bcc-2771eb2c6462
-- title:
--   A subnormal Hall subgroup is normal
-- statement:
--   Let $G$ be a finite group and let $H$ be a **Hall** subgroup of $G$, i.e. one with $\gcd(|H|,[G:H])=1$. If $H$ is subnormal in $G$, then $H$ is normal in $G$. This is immediate from Lemma 2.2: $P(|G/H_G|)=P([G:H])$, so no prime divisor of $|H|$ divides $|G/H_G|=[G:H]\cdot|H/H_G|$, forcing $H=H_G$. *Formalization note:* "Hall" is spelled `Nat.Coprime (Nat.card H) H.index`, which is the standard meaning in a finite group because `Nat.card ↥H * H.index = Nat.card G`; the conclusion is the Prop-valued class `Subgroup.Normal` used directly as the goal.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Corollary 2.1

import Mathlib

namespace SubnormalCover

/-- **Sun, Corollary 2.1.**

A subnormal Hall subgroup of a finite group is normal. A Hall subgroup is one whose order is
coprime to its index, which in a finite group is spelled `Nat.Coprime (Nat.card H) H.index`
since `Nat.card H * H.index = Nat.card G`. -/
theorem normal_of_isSubnormal_of_coprime {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hsn : H.IsSubnormal) (hHall : Nat.Coprime (Nat.card H) H.index) :
    H.Normal := by
  sorry

end SubnormalCover
