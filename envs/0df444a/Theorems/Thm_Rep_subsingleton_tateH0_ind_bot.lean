-- Prove2me | Theorems.Thm_Rep_subsingleton_tateH0_ind_bot
-- name    : Rep.subsingleton_tateH0_ind_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/04c5f66c-b274-521a-aee8-8d488f3f30e8
-- title:
--   Tate ̂ H⁰ vanishes for modules induced from bot
-- statement:
--   Let $k$ be a commutative ring and $G$ a group with finitely many elements, and let $A$ be an object of `Rep k (⊥ : Subgroup G)`, that is, a $k$-linear representation of the trivial subgroup of $G$ on a $k$-module. Apply `Rep.ind` along the inclusion homomorphism `(⊥ : Subgroup G).subtype` to obtain the induced representation of $G$, and form its `tateH0`: by definition this is the quotient of the $k$-module of invariants of the underlying representation $\rho$ by the image of the map `normBar`, the $k$-linear map from the coinvariants of $\rho$ to its invariants obtained by factoring the norm $\sum_{g \in G} \rho(g)$, viewed as a map into the invariants, through the coinvariants. The assertion is that this quotient is a subsingleton, i.e. has at most one element; since it is a quotient module, this says that $\hat H^0(G, \mathrm{Ind}_{\{1\}}^G A)$ vanishes, every $G$-invariant element of the induced representation being a norm.
--
--   This is the degree-$0$ half of the classical statement that modules induced from the trivial subgroup are cohomologically trivial, the input for dimension shifting in Tate cohomology. It is used by [`Rep.isZero_tateCohomology_indBot`](thm.html#Rep.isZero_tateCohomology_indBot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_subsingleton_tateH0_ind_bot.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.subsingleton_tateH0_ind_bot {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (A : Rep k (⊥ : Subgroup G)) : Subsingleton (Rep.ind (⊥ : Subgroup G).subtype A).tateH0 := by sorry
