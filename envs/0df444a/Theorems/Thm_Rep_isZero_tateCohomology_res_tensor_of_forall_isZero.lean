-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero
-- name    : Rep.isZero_tateCohomology_res_tensor_of_forall_isZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5f2e7343-5fbf-510d-85e8-05ac52133321
-- title:
--   Tensoring with a free ℤ-module preserves cohomological triviality
-- statement:
--   Let $G$ be a finite group, let $B$ be an object of `Rep ℤ G`, i.e. an abelian group with a $\mathbb{Z}$-linear $G$-action, and let $\rho$ be a representation of $G$ on an abelian group $V$ that is free as a $\mathbb{Z}$-module (no finiteness on $V$ is assumed). Assume that for every subgroup $S \le G$ and every $q \in \mathbb{Z}$ the module `(Rep.res S.subtype B).tateCohomology q` is a zero object of `ModuleCat ℤ`; here `tateCohomology` is defined by cases: group cohomology $H^{n+1}$ in degrees $n+1 \ge 1$, the invariants modulo the range of the map `normBar` in degree $0$, the kernel of `normBar` in degree $-1$, and group homology $H_{n+1}$ in degrees $-(n+2)$. Then for every subgroup $S \le G$ and every $q \in \mathbb{Z}$, the module `(Rep.res S.subtype (B ⊗ Rep.of ρ)).tateCohomology q` is likewise a zero object, the tensor product carrying the diagonal $G$-action and being restricted to $S$.
--
--   This is the standard permanence statement that cohomological triviality of a $G$-module $B$ (vanishing of Tate cohomology in all degrees over all subgroups) is inherited by $B \otimes_{\mathbb{Z}} V$ for $V$ a free abelian group with $G$-action. It is used in the Tate cup-product package, where it feeds [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_res_tensor_of_forall_isZero.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_res_tensor_of_forall_isZero {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (hB : ∀ (S : Subgroup G) [Fintype S] (q : ℤ), CategoryTheory.Limits.IsZero ((Rep.res S.subtype B).tateCohomology q))
    (S : Subgroup G) [Fintype S] (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (B ⊗ Rep.of ρ)).tateCohomology q) := by sorry
