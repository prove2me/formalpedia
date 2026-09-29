-- Prove2me | Theorems.Thm_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
-- name    : Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/6dd1e2d3-1390-52c4-a111-59ba80f80c81
-- title:
--   Detection of integer combinations by cyclic p'-subgroups
-- statement:
--   Let $p$ be a prime, let $G$ be a finite group, let $r$ be a natural number, and let $S : \mathrm{Fin}\ r \to \mathrm{Rep}\,(\mathbb{Z}/p)\,G$ be a family of representations of $G$ over $\mathbb{Z}/p$, each finite-dimensional over $\mathbb{Z}/p$, each with irreducible underlying representation $(S\,i).\rho$, and pairwise non-isomorphic in the sense that for all $i, j$ the existence of an isomorphism $S\,i \cong S\,j$ in $\mathrm{Rep}\,(\mathbb{Z}/p)\,G$ forces $i = j$. Let $n : \mathrm{Fin}\ r \to \mathbb{Z}$ be integers, and assume that for every subgroup $H \le G$ which is cyclic and whose cardinality $\operatorname{card} H$ is coprime to $p$, and for every finite-dimensional representation $T$ of $H$ over $\mathbb{Z}/p$, the integer identity $$\sum_i n_i \cdot \dim_{\mathbb{Z}/p} \operatorname{Hom}_{H}\bigl(T, \operatorname{Res}_{H} S\,i\bigr) = 0$$ holds, where $\operatorname{Hom}_H$ is the space of morphisms in $\mathrm{Rep}\,(\mathbb{Z}/p)\,H$ and $\operatorname{Res}_H$ denotes restriction along the inclusion $H \hookrightarrow G$. Then $n$ is the zero function, i.e. $n_i = 0$ for all $i$.
--
--   This is the characteristic-$p$ detection statement underlying Artin induction over $\mathbb{F}_p$: the class of a virtual $\mathbb{F}_p[G]$-module in the Grothendieck group is determined by the multiplicities of its restrictions to cyclic subgroups of order prime to $p$, a form of the linear independence of Brauer characters of the simple $\mathbb{F}_p[G]$-modules. It is used by [`Rep.eq_of_additive_of_forall_nonempty_res_iso`](thm.html#Rep.eq_of_additive_of_forall_nonempty_res_iso), where additive functions on representations agreeing after restriction to such subgroups are shown to agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {r : ℕ} (S : Fin r → Rep.{0} (ZMod p) G) [∀ i, FiniteDimensional (ZMod p) (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (n : Fin r → ℤ)
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
        ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0) :
    n = 0 := by sorry
