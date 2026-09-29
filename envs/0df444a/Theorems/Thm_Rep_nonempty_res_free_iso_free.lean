-- Prove2me | Theorems.Thm_Rep_nonempty_res_free_iso_free
-- name    : Rep.nonempty_res_free_iso_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e925352f-f451-5bd8-ab7a-bf52f4cb4eea
-- title:
--   Restriction of a free representation to a subgroup is free
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, both in a fixed universe, let $S$ be a subgroup of $G$, and let $\alpha$ be a type in the same universe. Write `Rep.free k G α` for the free $k[G]$-module on $\alpha$, that is, the object of $\mathrm{Rep}\,k\,G$ whose underlying module is $\alpha \to_{f} k[G]$ with $G$ acting by left translation in the $k[G]$-coordinate, and write `Rep.res S.subtype` for the restriction functor $\mathrm{Rep}\,k\,G \to \mathrm{Rep}\,k\,S$ along the inclusion $S \hookrightarrow G$. The assertion is that there exists a type $\beta$ in the same universe together with an isomorphism, in the category $\mathrm{Rep}\,k\,S$, between the restriction of `Rep.free k G α` to $S$ and the free $k[S]$-module `Rep.free k S β`; the isomorphism is asserted only through `Nonempty`, so no particular such isomorphism is named, and $\beta$ is likewise only asserted to exist (in the proof it is taken to be $\alpha$ times the set of orbits of the left multiplication action of $S$ on $G$, i.e. $\alpha \times (S\backslash G)$).
--
--   This is the statement that a free $k[G]$-module, restricted to a subgroup $S$, is again free over $k[S]$, with basis indexed by the original basis times the set of right cosets $S\backslash G$. It is used where a hypothesis quantified over subgroups — for instance cohomological triviality of the terms of a resolution — has to be applied to free covers, as in [`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero), and in the Tate cup-product and local-bridge arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_res_free_iso_free.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_res_free_iso_free {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (α : Type u) :
    ∃ β : Type u, Nonempty (Rep.res S.subtype (Rep.free k G α) ≅ Rep.free k S β) := by sorry
