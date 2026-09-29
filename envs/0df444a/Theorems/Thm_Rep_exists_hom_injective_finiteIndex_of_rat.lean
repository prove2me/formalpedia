-- Prove2me | Theorems.Thm_Rep_exists_hom_injective_finiteIndex_of_rat
-- name    : Rep.exists_hom_injective_finiteIndex_of_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/25da1b41-619d-5579-a0f0-1dcaedfbfd14
-- title:
--   Commensurability of two G-lattices in a rational representation
-- statement:
--   Let $G$ be a finite group, let $V$ be an abelian group equipped with a $\mathbb{Q}$-module structure, and let $\tau$ be a representation of $G$ on $V$ over $\mathbb{Q}$. Let $L$ and $L'$ be objects of `Rep ℤ G`, i.e. $\mathbb{Z}$-linear representations of $G$ with actions $L.\rho$ and $L'.\rho$, each finite as a $\mathbb{Z}$-module. Suppose given additive maps $i : L \to V$ and $i' : L' \to V$, each injective, each equivariant in the sense that $i(L.\rho(g)x) = \tau(g)(i(x))$ for all $g \in G$, $x \in L$, and similarly for $i'$, and suppose that the $\mathbb{Q}$-span of the range of $i$ and the $\mathbb{Q}$-span of the range of $i'$ are both all of $V$. The conclusion is that there exists a morphism $f : L \to L'$ in `Rep ℤ G` (an additive, $\mathbb{Z}$-linear, $G$-equivariant map) whose underlying map `f.hom` is injective and whose range, viewed as an additive subgroup of $L'$, has finite index.
--
--   This is the standard commensurability statement for two $G$-stable finitely generated lattices spanning the same rational representation of a finite group: after clearing denominators one lattice embeds $G$-equivariantly into the other with finite-index image. It is used to compare invariants of such lattices, and is cited in the proof of [`Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq`](thm.html#Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_injective_finiteIndex_of_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exists_hom_injective_finiteIndex_of_rat {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℚ V] (τ : Representation ℚ G V)
    {L L' : Rep ℤ G} [Module.Finite ℤ L] [Module.Finite ℤ L']
    (i : L →+ V) (hi : Function.Injective i) (hiG : ∀ (g : G) (x : L), i (L.ρ g x) = τ g (i x))
    (i' : L' →+ V) (hi' : Function.Injective i') (hi'G : ∀ (g : G) (x : L'), i' (L'.ρ g x) = τ g (i' x))
    (hfull : Submodule.span ℚ (Set.range i) = ⊤) (hfull' : Submodule.span ℚ (Set.range i') = ⊤) :
    ∃ f : L ⟶ L', Function.Injective f.hom ∧ (f.hom : L →+ L').range.FiniteIndex := by sorry
