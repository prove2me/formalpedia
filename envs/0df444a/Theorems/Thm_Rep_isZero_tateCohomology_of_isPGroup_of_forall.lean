-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_of_isPGroup_of_forall
-- name    : Rep.isZero_tateCohomology_of_isPGroup_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/ca94aa01-fc8c-5c98-ad7a-40be942e77b7
-- title:
--   Vanishing of Tate cohomology of a p-group via consecutive degrees
-- statement:
--   Fix a commutative ring $k$, a finite group $P$ and a prime $p$, and assume `hP` that $P$ is a $p$-group (every element has order a power of $p$, in Mathlib's `IsPGroup` sense). Let $B$ be a $k$-linear representation of $P$. The hypothesis `h` is that for every finite group $Q$ (in the same universe) and every injective group homomorphism $g \colon Q \to P$ there is some integer $q$ for which the Tate cohomology of the restricted representation `Rep.res g B` vanishes in the two consecutive degrees $q$ and $q+1$, vanishing meaning that the corresponding object of `ModuleCat k` is a zero object. Here `tateCohomology` is defined degreewise: in degrees $n \ge 1$ it is ordinary group cohomology $H^n$, in degree $0$ the invariants modulo the range of the map `normBar` induced by the norm, in degree $-1$ the kernel of `normBar`, and in degree $-(m+2)$ the group homology $H_{m+1}$. The conclusion is that for every integer $n$ the Tate cohomology of $B$ itself in degree $n$ is zero. Thus the hypothesis is imposed not only at $P$ but at every group embeddable in $P$, while the conclusion is asserted at $P$ alone.
--
--   This is the $p$-group case of the Nakayama–Tate vanishing criterion: vanishing of Tate cohomology in two consecutive degrees on every subgroup of a finite $p$-group forces vanishing in all degrees. It feeds the general finite-group statement [`Rep.isZero_tateCohomology_res_of_forall_isPGroup`](thm.html#Rep.isZero_tateCohomology_res_of_forall_isPGroup), obtained by passing to the Sylow subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_of_isPGroup_of_forall.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_of_isPGroup_of_forall {k P : Type u} [CommRing k] [Group P] [Fintype P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (B : Rep.{u} k P)
    (h : ∀ (Q : Type u) [Group Q] [Fintype Q] (g : Q →* P), Function.Injective g →
      ∃ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology q) ∧
        CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology (q + 1)))
    (n : ℤ) : CategoryTheory.Limits.IsZero (B.tateCohomology n) := by sorry
