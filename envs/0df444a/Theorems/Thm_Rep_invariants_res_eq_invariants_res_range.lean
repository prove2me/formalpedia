-- Prove2me | Theorems.Thm_Rep_invariants_res_eq_invariants_res_range
-- name    : Rep.invariants_res_eq_invariants_res_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/eddf0a19-71a0-53fa-bf6d-ca56fb5f43c0
-- title:
--   Invariants of a restricted representation depend only on the image
-- statement:
--   Let $k$ be a commutative ring (a type in the lowest universe), let $G$ and $D'$ be groups, let $\varphi : D' \to G$ be a group homomorphism, and let $X$ be a $k$-linear representation of $G$, i.e. an object of `Rep k G` with underlying module in the lowest universe. Two restrictions of $X$ are compared: the restriction `Rep.res φ X` along $\varphi$, which is the underlying $k$-module of $X$ with $D'$ acting through $d \mapsto \rho_X(\varphi(d))$, and the restriction `Rep.res φ.range.subtype X` along the inclusion of the image subgroup $\varphi(D') \le G$, on which $\varphi(D')$ acts by the corresponding values of $\rho_X$. The assertion is that the submodules of invariants of these two representations coincide as submodules of the underlying module of $X$: a vector $v$ is fixed by $\rho_X(\varphi(d))$ for every $d \in D'$ if and only if it is fixed by $\rho_X(g)$ for every $g$ in the range of $\varphi$. The statement is an equality of submodules, not merely an isomorphism of representations.
--
--   This is the elementary observation that taking invariants along a homomorphism only sees its image, used as a bridge between a representation restricted along a map of groups and the same representation restricted to the corresponding subgroup. It is invoked in the computation of the rank of the invariants of a coinduced module at an archimedean place, [`groupCohomology.finrank_invariants_archimedean_coind`](thm.html#groupCohomology.finrank_invariants_archimedean_coind).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_invariants_res_eq_invariants_res_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.invariants_res_eq_invariants_res_range
    {k : Type} [CommRing k] {G D' : Type} [Group G] [Group D'] (φ : D' →* G) (X : Rep.{0} k G) :
    (Rep.res φ X).ρ.invariants = (Rep.res φ.range.subtype X).ρ.invariants := by sorry
