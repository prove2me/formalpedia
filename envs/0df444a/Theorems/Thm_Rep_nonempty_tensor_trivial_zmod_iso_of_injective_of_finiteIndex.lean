-- Prove2me | Theorems.Thm_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
-- name    : Rep.nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/dab3911e-58e9-5b8f-9319-c6c8afcefd93
-- title:
--   Commensurable ℤ[G]-lattices have isomorphic mod p reductions
-- statement:
--   Let $G$ be a finite group and $p$ a prime such that the cardinality of $G$ is coprime to $p$. Let $L$ and $L'$ be objects of `Rep ℤ G`, that is, $\mathbb{Z}$-linear representations of $G$, each finitely generated and free as a $\mathbb{Z}$-module, and let $f : L \to L'$ be a morphism of representations whose underlying $\mathbb{Z}$-linear map is injective and whose image, viewed as a subgroup of the additive group of $L'$, has finite index. The conclusion asserts that the type of isomorphisms in `Rep ℤ G` from $L \otimes \mathbf{1}_{\mathbb{Z}/p}$ to $L' \otimes \mathbf{1}_{\mathbb{Z}/p}$ is nonempty, where $\mathbf{1}_{\mathbb{Z}/p}$ denotes `Rep.trivial ℤ G (ZMod p)`, the $\mathbb{Z}$-module $\mathbb{Z}/p$ with trivial $G$-action, and $\otimes$ is the monoidal product of `Rep ℤ G`; concretely, the reductions $L/pL$ and $L'/pL'$ are isomorphic as $\mathbb{F}_p[G]$-modules. Only the existence of such an isomorphism is asserted, not a distinguished one.
--
--   This is the well-definedness statement underlying the decomposition map on lattices: commensurable $G$-stable lattices in the same rational representation have isomorphic reductions modulo a prime $p$ not dividing $|G|$, the hypothesis on $|G|$ being essential. It is used by [`Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq`](thm.html#Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq), where mod $p$ reductions are compared through invariants of rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (f : L ⟶ L') (hf : Function.Injective f.hom) (hfi : (f.hom : L →+ L').range.FiniteIndex) :
    Nonempty (L ⊗ Rep.trivial ℤ G (ZMod p) ≅ L' ⊗ Rep.trivial ℤ G (ZMod p)) := by sorry
