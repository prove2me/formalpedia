-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_6_1
-- name    : TangleStructTree.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:55.64554+00:00
-- url     : https://prove2.me/theorems/caa14704-a6aa-4c21-a329-9b8ae2a73196
-- title:
--   Theorem 6.1 — standard rich $\mathcal F$ admits an efficient irreducible ordered $\mathcal F$-tangle structure tree (corrected: finite separation system)
-- statement:
--   Let $\vec S$ be a **finite** ordered separation system, and let $\mathcal F$ be a set that is standard and rich for $\vec S$. Then $\vec S$ has an $\mathcal F$-tangle structure tree that is at the same time
--
--   1. efficient,
--   2. irreducible, and
--   3. ordered.
--
--   This is the existence theorem for the paper's best structure trees: one tree displays all $\mathcal F$-tangles with no unnecessary edges, the minimal elements of every tangle along its root path, and lower-order separations nearer the root.
--
--   Differences from the source:
--   - correction: any ordered separation system S⃗ → [Finite E]; reason: the statement is false for infinite S⃗: take S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ} with the trivial order, ∗ swapping s⃗_n and s⃖_n, all orders 0, ℱ = ∅ (standard: nothing is trivial; rich vacuously); the closure of a finite label set orients only finitely many s_n and no leaf is forbidden, so no ℱ-tangle structure tree exists. The same correction as the published TangleStructTree.theorem_4_6, which the paper's proof invokes
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 6.1, p.16 (PDF 27); = extended abstract Theorem 6.1, p.7

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
import Definitions.Def_TangleStructTree_Supplement_IsIrreducible
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 6.1** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.16 (PDF 27); = extended abstract Theorem 6.1, p.7), corrected: finite
separation system. Let `S⃗` be an ordered separation system. If a set `ℱ` is standard and rich for
`S⃗`, then `S⃗` has an efficient and irreducible ordered `ℱ`-tangle structure tree.

**Formalization Note**
1. Correction: `S⃗` is finite (`Finite E`), as in the published `TangleStructTree.theorem_4_6`.
   For infinite `S⃗` the statement fails: take `S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ}` pairwise incomparable,
   all orders `0`, `ℱ = ∅` (standard and rich); every leaf label set of a finite tree leaves some
   `s_n` unoriented, so no leaf is a tangle leaf or forbidden and no `ℱ`-tangle structure tree
   exists.
2. `IsIrreducible T ℱ` includes `T.IsTST ℱ` (being an `ℱ`-tangle structure tree).
3. The order function is `ord : E → ℝ` with `ord (x∗) = ord x`. -/
theorem theorem_6_1 [Finite E] (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hstd : IsStandard ℱ) (hrich : IsRich ord ℱ) :
    ∃ T : SepTree E, IsIrreducible T ℱ ∧ IsEfficientTree T ord ∧ IsOrderedTree T ord := by sorry

end Supplement

end TangleStructTree
