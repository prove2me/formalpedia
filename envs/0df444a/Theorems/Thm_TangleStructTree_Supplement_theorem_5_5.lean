-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_5_5
-- name    : TangleStructTree.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:22.908724+00:00
-- url     : https://prove2.me/theorems/2bf1ffbd-2291-4b76-baa4-9d24e768a78d
-- title:
--   Theorem 5.5 — contraction to an irreducible $\mathcal F$-tangle structure tree that keeps leaves, tangles and tangle nodes
-- statement:
--   Let $\vec S$ be a separation system and $\mathcal F$ any set. For every $\mathcal F$-tangle structure tree $T$ of $\vec S$ there is an **irreducible** $\mathcal F$-tangle structure tree $T'$ of $\vec S$ obtained from $T$ by a sequence $T=T^1,\dots,T^n=T'$ with $T^{i+1}=T^i_{w\to v}$ for suitable nodes $v,w$ of $T^i$ ($w$ a child of $v$). Identifying $V(T')$ with a subset of $V(T)$ as usual:
--
--   1. $T'$ imposes the same partial ordering on its nodes as $T$; in particular $T'$ is ordered if $T$ is (for any order function).
--   2. Every leaf $\ell$ of $T'$ is a leaf of $T$, and its incident edge in $T$ is still an edge of $T'$.
--   3. The tangle leaves of $T'$ are precisely those of $T$, and their tangles $\lfloor\beta_\ell\rfloor$ are the same in $T'$ as in $T$.
--   4. The tangle nodes of $T'$ are precisely those of $T$.
--   5. A tangle node $v$ separates two tangle leaves in $T'$ if and only if it separates them in $T$.
--
--   Contracting unnecessary edges thus removes redundancy from a tangle structure tree without losing any of the tangle structure it displays.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: T′ obtained from T by T^{i+1} = T^i_{w→v}, with V(T_{w→v}) regarded as a subset of V(T) → ContractsTo T T′ ι (refl and genuine contraction steps), ι the composite identification; every conclusion is stated through ι, with ι injective on V(T′) and into V(T); reason: this is the paper's convention V(T_{w→v}) ⊆ V(T) made explicit
--   - encoding: "precisely those of T" (tangle leaves, tangle nodes) → ι maps those of T′ into and onto those of T; reason: with ι injective this is equality of the sets under the identification
--   - reading: tangle node: a tangle leaf ℓ ≥_r w for every successor w of v in >_r → for every child w = x :: v of v; reason: the paper uses "successor" for a child ("a node of T with a successor w, let s⃗ := β(vw)", Lemma 5.1); with "any descendant" Corollary 5.3 and this clause fail as soon as a deleted subtree holds a forbidden leaf
--   - reading: v separates two tangle leaves → they lie above distinct children of v; reason: the proof: "s_v distinguishes two tangles if and only if v separates their tangle leaves"
--   - reading: T′ is ordered if T is (S⃗ carries no fixed order function in this theorem) → for every order function ord: ordered for ord ⇒ ordered for ord; reason: "ordered" is defined relative to an order function; the theorem holds for each
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 5.5, p.15 (PDF 26); = extended abstract Theorem 5.1, p.6

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_ContractsTo
import Definitions.Def_TangleStructTree_Supplement_IsIrreducible
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree
import Definitions.Def_TangleStructTree_Supplement_IsTangleNode

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 5.5** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.15 (PDF 26); = extended abstract Theorem 5.1, p.6). Let `S⃗` be a
separation system, and let `ℱ` be any set. For every `ℱ`-tangle structure tree `T` of `S⃗` there
exists an irreducible `ℱ`-tangle structure tree `T′` of `S⃗` obtained from `T` by a sequence
`T = T^1, …, T^n = T′` with `T^{i+1} = T^i_{w→v}` for suitable nodes `v, w` of `T^i`.
The tree `T′` imposes the same partial ordering on its nodes as `T` does. In particular, `T′` is
ordered if `T` is. Its leaves `ℓ` are also leaves of `T`, and their incident edges in `T` are
still edges of `T′`.
The tangle leaves `ℓ` of `T′` are precisely those of `T`. Their associated tangles `⌊β_ℓ⌋` are
the same in `T′` as in `T`. The tangle nodes of `T′` are precisely those of `T`. A tangle node
`v` separates two tangle leaves in `T′` if and only if it separates them in `T`.

**Formalization Note**
1. `ContractsTo T T′ ι` records the sequence of contractions `T^{i+1} = T^i_{w→v}` (`w` a child
   of `v` in `T^i`) and the composite identification `ι` of the nodes of `T′` with nodes of `T`
   (the paper's convention `V(T_{w→v}) ⊆ V(T)`). The conclusions are stated through `ι`.
2. Nodes are root-path label lists, newest first, so the tree order `u ≤_r u′` is `u <:+ u′`.
3. `S⃗` carries no fixed order function here; "ordered" is stated for every order function `ord`.
4. "Incident edge kept": if `ι ℓ` has parent `p` in `T` via the edge labelled `x`, then `ℓ` has
   a parent `p′` in `T′` via an edge labelled `x`, with `ι p′ = p`.
5. "Precisely those of `T`": `ι` maps the tangle leaves (tangle nodes) of `T′` into, and onto,
   those of `T`; with `ι` injective this is equality of the sets under the identification.
6. Tangle nodes are read with "successor" = child (`IsTangleNode`), and `v` separates `ℓ, ℓ′`
   when they lie above distinct children of `v` (`Separates`). -/
theorem theorem_5_5 (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) :
    ∃ (T' : SepTree E) (ι : List E → List E), ContractsTo T T' ι ∧ IsIrreducible T' ℱ ∧
      (∀ u ∈ T'.nodes, ι u ∈ T.nodes) ∧ Set.InjOn ι (T'.nodes : Set (List E)) ∧
      (∀ u ∈ T'.nodes, ∀ u' ∈ T'.nodes, (u <:+ u' ↔ ι u <:+ ι u')) ∧
      (∀ ord : E → ℝ, IsOrderFunction ord → IsOrderedTree T ord → IsOrderedTree T' ord) ∧
      (∀ ℓ : List E, T'.IsLeaf ℓ → T.IsLeaf (ι ℓ) ∧
        ∀ (x : E) (p : List E), ι ℓ = x :: p → ∃ p' : List E, ℓ = x :: p' ∧ ι p' = p) ∧
      (∀ ℓ : List E, T'.IsTangleLeaf ℱ ℓ → T.IsTangleLeaf ℱ (ι ℓ)) ∧
      (∀ m : List E, T.IsTangleLeaf ℱ m → ∃ ℓ : List E, T'.IsTangleLeaf ℱ ℓ ∧ ι ℓ = m) ∧
      (∀ ℓ : List E, T'.IsTangleLeaf ℱ ℓ → sepClosure (labels ℓ) = sepClosure (labels (ι ℓ))) ∧
      (∀ v : List E, IsTangleNode T' ℱ v → IsTangleNode T ℱ (ι v)) ∧
      (∀ m : List E, IsTangleNode T ℱ m → ∃ v : List E, IsTangleNode T' ℱ v ∧ ι v = m) ∧
      (∀ v ℓ₁ ℓ₂ : List E, IsTangleNode T' ℱ v → T'.IsTangleLeaf ℱ ℓ₁ → T'.IsTangleLeaf ℱ ℓ₂ →
        (Separates v ℓ₁ ℓ₂ ↔ Separates (ι v) (ι ℓ₁) (ι ℓ₂))) := by sorry

end Supplement

end TangleStructTree
