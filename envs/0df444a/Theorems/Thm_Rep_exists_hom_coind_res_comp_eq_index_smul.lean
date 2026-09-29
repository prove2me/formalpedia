-- Prove2me | Theorems.Thm_Rep_exists_hom_coind_res_comp_eq_index_smul
-- name    : Rep.exists_hom_coind_res_comp_eq_index_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e74f7168-f72a-540b-bffa-aa227c56766c
-- title:
--   Unit and trace for coind_S^Gres N, with composite [G:S]
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $S \le G$ a subgroup of finite index, and $N$ a $k$-linear representation of $G$ (all in a single universe). Write $I =$ `Rep.coind S.subtype (Rep.res S.subtype N)` for the representation coinduced along the inclusion $S \hookrightarrow G$ from the restriction of $N$ to $S$: its elements are functions $f \colon G \to N$ satisfying $f(sg) = \rho(s) f(g)$ for $s \in S$, with $G$ acting by right translation. The assertion is that there exist morphisms of representations $\iota \colon N \to I$ and $\tau \colon I \to N$ such that: (i) for every $n \in N$ and $g \in G$ the function underlying $\iota(n)$ takes the value $\rho(g)\,n$ at $g$; (ii) for every $f \in I$ one has $\tau(f) = \sum^{\mathrm f}_{q \in G/S} \rho(q_{\mathrm{out}})\bigl(f(q_{\mathrm{out}}^{-1})\bigr)$, a finite sum (`finsum`) over the coset space, where $q_{\mathrm{out}}$ denotes the chosen representative of the coset $q$; (iii) the $k$-linear map underlying $\tau$ is surjective; and (iv) $\tau(\iota(n)) = (\,[G:S] : k\,)\cdot n$ for all $n \in N$, the index being cast into $k$.
--
--   This is the unit of the restriction–coinduction adjunction together with the trace (counit at finite index), whose composite is multiplication by $[G:S]$; consequently $N$ is a direct summand of $\mathrm{coind}_S^G\mathrm{res}_S^G N$ whenever $[G:S]$ is invertible in $k$. It is used in the cohomological part of the development, where it feeds results on restriction maps and on surjectivity in degree $2$ for continuous cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_coind_res_comp_eq_index_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_hom_coind_res_comp_eq_index_smul {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.FiniteIndex] (N : Rep.{u} k G) :
    ∃ (ι : N ⟶ Rep.coind S.subtype (Rep.res S.subtype N)) (τ : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N),
      (∀ (n : N) (g : G), ((ι.hom n : Rep.coind S.subtype (Rep.res S.subtype N)) : G → N) g = N.ρ g n) ∧
      (∀ f : Rep.coind S.subtype (Rep.res S.subtype N),
        τ.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹)) ∧
      Function.Surjective τ.hom ∧
      ∀ n : N, τ.hom (ι.hom n) = (S.index : k) • n := by sorry
