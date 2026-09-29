-- Prove2me | Theorems.Thm_Subgroup_exists_int_forall_finsum_ite_eq_one
-- name    : Subgroup.exists_int_forall_finsum_ite_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/963a3bba-aa83-5e29-9940-5472cdd3a434
-- title:
--   Existence of Artin induction coefficients on cyclic p'-subgroups
-- statement:
--   Let $p$ be a natural number and let $G$ be a finite group. Then there exists a function $b$ from the subgroups of $G$ to $\mathbb{Z}$ with the following property: for every subgroup $H \le G$ which is cyclic and whose order $\lvert H \rvert$ (the `Nat.card` of $H$) is coprime to $p$, the finite sum, taken over all subgroups $D$ of $G$, of the expression which equals $b(D)$ when $D$ is cyclic, $\lvert D \rvert$ is coprime to $p$ and $H \le D$, and equals $0$ otherwise, is equal to $1$. Since $G$ is finite its subgroup lattice is finite, so the `finsum` over all subgroups is an ordinary finite sum; equivalently, for each cyclic $p'$-subgroup $H$ one has $\sum_{D} b(D) = 1$, the sum ranging over the cyclic subgroups $D \ge H$ of order coprime to $p$. Only the existence of such a family of integers is asserted; no formula for $b$, and no condition on $b(D)$ for subgroups $D$ that are not cyclic $p'$-subgroups, is part of the statement.
--
--   These are the integral coefficients underlying Artin's induction theorem for the trivial character, restricted to cyclic subgroups of order coprime to $p$; classically one may take $b(D) = \sum_{C \ge D} \mu([C:D])$ over cyclic $p'$-overgroups, but only existence is needed downstream. It is used in [`Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime`](thm.html#Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime), which deduces the vanishing of an additive invariant of representations from its vanishing on representations induced from cyclic $p'$-subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_exists_int_forall_finsum_ite_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Subgroup.exists_int_forall_finsum_ite_eq_one (p : ℕ) {G : Type} [Group G] [Finite G] :
    ∃ b : Subgroup G → ℤ, ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1 := by sorry
