-- Prove2me | Theorems.Thm_TangleStructTree_theorem_4_8
-- name    : TangleStructTree.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:05.990344+00:00
-- url     : https://prove2.me/theorems/a3f8efc2-877b-41a8-90fd-f9b3f25bbbeb
-- title:
--   Theorem 4.8 — for injective order functions: a thoroughly ordered $\mathcal F$-tangle structure tree exists iff $\mathcal F$ is rich, and it is unique (corrected: finite $\vec S$ for existence)
-- statement:
--   Let $\vec S$ be a separation system with an order function that is injective on $S$, and let $\mathcal F$ be a set that is standard for $\vec S$. Then
--
--   1. if $\vec S$ is finite and $\mathcal F$ is rich for $\vec S$, there exists a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$;
--   2. if there exists a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$, then $\mathcal F$ is rich for $\vec S$;
--   3. if one exists, it is unique.
--
--   Items 1 and 2 are the two directions of the paper's "if and only if".
--
--   For injective order functions the rich sets $\mathcal F$ are exactly those that admit a canonical, uniquely determined structure tree.
--
--   Differences from the source:
--   - correction: any separation system S⃗ (in the existence statement) → hypothesis `Finite E` on the existence clause (rich ⇒ a tree exists) only; the other clauses hold for every separation system; reason: the existence clause is false for infinite S⃗: take S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ} with the trivial order (x ≤ y iff x = y), ∗ swapping s⃗_n and s⃖_n, all orders 0 and ℱ = ∅; ℱ is standard (nothing is trivial) and rich (nothing has a subset in ∅); an ℱ-tangle structure tree has no forbidden leaf, so it has a tangle leaf ℓ, but ⌊β_ℓ⌋ = β_ℓ is finite and orients only finitely many s_n. The paper's proof uses exactly finiteness (journal version p.7: paths have length at most |S|; p.10: termination by Corollary 3.5)
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: the ℱ-tangle structure tree is unique → any two such SepTrees are equal; reason: equality of SepTrees is uniqueness up to root- and label-preserving isomorphism of rooted edge-labelled trees
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 4.8, p.11 (PDF 22)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 4.8** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.11 (PDF 22)), corrected: finite
separation system in the existence direction. Let `S⃗` be a separation system with an injective order function on `S`, and let
`ℱ` be a set that is standard for `S⃗`. There exists a thoroughly ordered `ℱ`-tangle structure tree
of `S⃗` if and only if `ℱ` is rich for `S⃗`. If one exists, it is unique.

**Formalization Note** The finiteness of `S⃗` is a correction, assumed (as the hypothesis
`Finite E`) only for the direction "rich ⇒ a tree exists", which is false for infinite `S⃗` (see
Theorem 4.6); the converse direction and uniqueness are stated for every separation system. The
two directions of the "if and only if" are the first two conjuncts. "Unique" is equality of
`SepTree`s, i.e. uniqueness up to root- and label-preserving isomorphism. -/
theorem theorem_4_8 (ord : E → ℝ) (hord : IsOrderFunction ord) (hinj : OrderInjective ord)
    (ℱ : Set (Set E)) (hstd : IsStandard ℱ) :
    (Finite E → IsRich ord ℱ → ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) ∧
      ((∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) → IsRich ord ℱ) ∧
      ∀ T T' : SepTree E, T.ThoroughlyOrdered ord → T.IsTST ℱ →
        T'.ThoroughlyOrdered ord → T'.IsTST ℱ → T = T' := by sorry

end TangleStructTree
