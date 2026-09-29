-- Prove2me | Theorems.Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
-- name    : Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/35f84320-ee57-5608-a3a9-0a20d9a59d1f
-- title:
--   Fibre degrees of a double coset degeneracy map sum to [K:K']
-- statement:
--   Let $G$ be a group, let $H, K, K'$ be subgroups of $G$ with $K' \le K$, and let $x \in G$; assume the relative index of $K'$ in $K$ is finite (`Subgroup.IsFiniteRelIndex`, i.e. $K' \cap K$ has finite index in $K$), and assume the subtype of those classes $c$ in the double coset space $H \backslash G / K'$ whose chosen representative $\tilde c$ (the `Quotient.out` of $c$) satisfies $H\tilde c K = H x K$ is a finite type. The assertion is that, summing over this fibre of $H \backslash G / K' \to H \backslash G / K$ above the class of $x$, $$\sum_{c} \bigl[\,H \cap \tilde c K \tilde c^{-1} \; : \; H \cap \tilde c K' \tilde c^{-1}\,\bigr] = [K : K' \cap K],$$ where the summand is the Mathlib relative index of $H \cap \tilde c K' \tilde c^{-1}$ in $H \cap \tilde c K \tilde c^{-1}$, the conjugates being formed as the images of $K'$ and $K$ under conjugation by $\tilde c$, and the right-hand side is the relative index of $K'$ in $K$. Note that each summand is written using the specific representative $\tilde c$ rather than an arbitrary one.
--
--   This is the degree formula for a degeneracy (level-forgetting) map of double coset spaces: the fibre of $H \backslash G / K' \to H \backslash G / K$ over a class $HxK$, with each class weighted by the index of the associated arithmetic subgroups, has total weight $[K:K']$; it is the orbit–stabiliser count for the action of $H \cap xKx^{-1}$ on $K/K'$. It is used in the construction of degeneracy data between adelic class sets, where it supplies the total degree of the forgetful map and of its shift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MulAction

theorem Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
    {G : Type*} [Group G] (H K K' : Subgroup G) (hK : K' ≤ K) (x : G) [K'.IsFiniteRelIndex K]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x},
      (H ⊓ K'.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj c.1.out).toMonoidHom) =
        K'.relIndex K := by sorry
