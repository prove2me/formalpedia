-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_6_5
-- name    : TangleStructTree.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:38.743169+00:00
-- url     : https://prove2.me/theorems/be196c00-9c4e-46bf-a8fc-00cdb67d95cc
-- title:
--   Theorem 6.5 — tangle-tree duality: an $\mathcal F$-tangle or an $\mathcal F$-tree, exactly one (corrected: finite separation system)
-- statement:
--   Let $\vec S$ be a **finite** ordered separation system, and let $\mathcal F$ be a set that is standard and rich for $\vec S$. Then exactly one of the following holds:
--
--   1. there exists an $\mathcal F$-tangle of $S$;
--   2. there exists an $\mathcal F$-tree of $\vec S$ (an $\mathcal F$-tangle structure tree all of whose leaves are forbidden).
--
--   In the case of (2), the $\mathcal F$-tree can be chosen to be irreducible, efficient and ordered.
--
--   This is a duality theorem for $\mathcal F$-tangles in which $\mathcal F$ need not consist of stars: an $\mathcal F$-tree is a certificate that no $\mathcal F$-tangle exists.
--
--   Differences from the source:
--   - correction: any ordered separation system S⃗ → [Finite E]; reason: the statement is false for infinite S⃗: take S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ} with the trivial order, ∗ swapping s⃗_n and s⃖_n, all orders 0, ℱ the set of all orientations of S (standard: nothing is trivial; rich: each orientation is strongly efficient in itself); there is no ℱ-tangle, and no leaf of a finite tree is forbidden because a finite label set contains no infinite element of ℱ, so neither (i) nor (ii) holds. The paper's proof invokes Theorem 6.1, which needs finiteness
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
--   - encoding: exactly one of (i), (ii) holds; in the case of (ii) the tree can be chosen with further properties → (i) ↔ ¬ (ii), and (ii) → ∃ one tree with all the properties together; reason: "exactly one" is (i) or (ii) but not both; the chosen tree is a single tree
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 6.5, pp.19–20 (PDF 30–31); = extended abstract Theorem 6.3, p.8

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_IsFTree
import Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
import Definitions.Def_TangleStructTree_Supplement_IsIrreducible
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 6.5** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), pp.19–20 (PDF 30–31); = extended abstract Theorem 6.3, p.8), corrected:
finite separation system. Let `S⃗` be an ordered separation system, and let `ℱ` be any set that is
standard and rich for `S⃗`. Then exactly one of the following assertions holds:
(i) there exists an `ℱ`-tangle of `S`;
(ii) there exists an `ℱ`-tree of `S⃗`.
In the case of (ii), the `ℱ`-tree can be chosen to be irreducible, efficient and ordered.

**Formalization Note**
1. Correction: `S⃗` is finite (`Finite E`). For infinite `S⃗` the statement fails: take
   `S⃗ = {s⃗_n, s⃖_n : n ∈ ℕ}` pairwise incomparable, all orders `0`, and `ℱ` the set of all
   orientations of `S` (standard: nothing is trivial; rich: every `σ ∈ ℱ` is strongly efficient in
   itself). There is no `ℱ`-tangle, and no leaf of a finite tree is forbidden, since a finite label
   set contains no infinite element of `ℱ`; so neither (i) nor (ii) holds.
2. "Exactly one" is `(i) ↔ ¬ (ii)`. "Chosen to be irreducible, efficient and ordered" is one tree
   with all these properties together, given (ii).
3. An `ℱ`-tree is an `ℱ`-tangle structure tree all of whose leaves are forbidden (`IsFTree`). -/
theorem theorem_6_5 [Finite E] (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hstd : IsStandard ℱ) (hrich : IsRich ord ℱ) :
    ((∃ τ : Set E, IsTangle ℱ τ) ↔ ¬ ∃ T : SepTree E, IsFTree T ℱ) ∧
      ((∃ T : SepTree E, IsFTree T ℱ) →
        ∃ T : SepTree E, IsFTree T ℱ ∧ IsIrreducible T ℱ ∧ IsEfficientTree T ord ∧
          IsOrderedTree T ord) := by sorry

end Supplement

end TangleStructTree
