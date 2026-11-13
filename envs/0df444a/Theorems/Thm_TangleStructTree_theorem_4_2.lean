-- Prove2me | Theorems.Thm_TangleStructTree_theorem_4_2
-- name    : TangleStructTree.theorem_4_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:56.281953+00:00
-- url     : https://prove2.me/theorems/149f0f4b-9866-49ca-b523-2f4999cf87b5
-- title:
--   Theorem 4.2 (extended abstract) — rich $\mathcal F$ has a thoroughly ordered $\mathcal F$-tangle structure tree; injective order: unique, forces richness (corrected: finite $\vec S$ for existence)
-- statement:
--   Let $\vec S$ be an ordered separation system, with order function $s\mapsto|s|$, and let $\mathcal F$ be standard for $\vec S$. Then:
--
--   1. if $\vec S$ is finite and $\mathcal F$ is rich, there exists a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$;
--   2. if the order function on $S$ is injective, a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$ is unique if it exists;
--   3. if the order function on $S$ is injective, the existence of a thoroughly ordered $\mathcal F$-tangle structure tree of $\vec S$ implies that $\mathcal F$ is rich.
--
--   This is the main result of the extended abstract (journal version Theorems 4.6 and 4.8): it characterizes the types of tangle, in an arbitrary separation system, for which a single tree displays all tangles together with certificates from $\mathcal F$ for all non-tangles.
--
--   Differences from the source:
--   - correction: any separation system S⃗ (in the existence statement) → hypothesis `Finite E` on the existence clause (rich ⇒ a tree exists) only; the other clauses hold for every separation system; reason: the existence clause is false for infinite S⃗: take S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ} with the trivial order (x ≤ y iff x = y), ∗ swapping s⃗_n and s⃖_n, all orders 0 and ℱ = ∅; ℱ is standard (nothing is trivial) and rich (nothing has a subset in ∅); an ℱ-tangle structure tree has no forbidden leaf, so it has a tangle leaf ℓ, but ⌊β_ℓ⌋ = β_ℓ is finite and orients only finitely many s_n. The paper's proof uses exactly finiteness (journal version p.7: paths have length at most |S|; p.10: termination by Corollary 3.5)
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: the ℱ-tangle structure tree is unique → any two such SepTrees are equal; reason: equality of SepTrees is uniqueness up to root- and label-preserving isomorphism of rooted edge-labelled trees
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), extended abstract, Theorem 4.2, p.6 (PDF 6); = journal version (Part I), Theorems 4.6 and 4.8, pp.10–11 (PDF 21–22)

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

/-- **Theorem 4.2** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), extended abstract, p.6 (PDF 6); = journal version
Theorems 4.6 and 4.8), corrected: finite separation system in the existence clause. Let `S⃗` be an ordered separation
system, and let `ℱ` be standard for `S⃗`. If `ℱ` is rich, there exists a thoroughly ordered
`ℱ`-tangle structure tree of `S⃗`. If the order function on `S` is injective, this `ℱ`-tangle
structure tree is unique if it exists, and its existence implies that `ℱ` is rich.

**Formalization Note**
1. The finiteness of `S⃗` is a correction, assumed (as the hypothesis `Finite E`) only in the
   existence clause: the proof uses that `S` is finite (journal version p.7 and p.10), and
   existence fails for infinite `S` (`S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ}` with the trivial order, all orders
   `0`, `ℱ = ∅`). Uniqueness and the converse are stated for every separation system.
2. Separation trees are encoded as finite prefix-closed sets of root-path label lists (`SepTree`);
   "unique" is equality of `SepTree`s, i.e. uniqueness up to root- and label-preserving isomorphism.
3. The order function is `ord : E → ℝ` with `ord (x∗) = ord x` (`IsOrderFunction`). -/
theorem theorem_4_2 (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hstd : IsStandard ℱ) :
    (Finite E → IsRich ord ℱ → ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) ∧
      (OrderInjective ord → ∀ T T' : SepTree E, T.ThoroughlyOrdered ord → T.IsTST ℱ →
        T'.ThoroughlyOrdered ord → T'.IsTST ℱ → T = T') ∧
      (OrderInjective ord → (∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) →
        IsRich ord ℱ) := by sorry

end TangleStructTree
